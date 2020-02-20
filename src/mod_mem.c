/*
 * File:
 *   mod_mem_mem.c
 * Author(s):
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * Description:
 *   Module for user callback and for dynamic memory management.
 *
 * Copyright (c) 2007-2014.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation, version 2
 * of the License.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * This program has a dual license and can also be distributed
 * under the terms of the MIT license.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "mod_mem.h"

#include "stm_internal.h"
#include "utils.h"
#include "gc.h"


#define MALLOC_FROM_POINTER(icb, m)     ((stm_malloc_t){ .idx = (m) - icb->abort })
#define FREE_FROM_POINTER(icb, f)       ((stm_free_t){ .idx = (f) - icb->commit })
#define POINTER_FROM_MALLOC(icb, m)     (__builtin_types_compatible_p(typeof(m), stm_malloc_t) ? icb->abort + (m).idx : NULL)
#define POINTER_FROM_FREE(icb, f)       (__builtin_types_compatible_p(typeof(f), stm_free_t) ? icb->commit + (f).idx : NULL)
#define MALLOC_VALID(icb, m)            (__builtin_types_compatible_p(typeof(m), stm_malloc_t) && (m).idx < icb->abort_nb)
#define FREE_VALID(icb, f)              (__builtin_types_compatible_p(typeof(f), stm_free_t) && (f).idx < icb->commit_nb)


/* ################################################################### *
 * TYPES
 * ################################################################### */

struct mod_mem_commit_entry {           /* Callback entry */
  const void *arg;                      /* Argument to be passed to function */
#if OPERATION_LOGGING != OPLOG_NONE
  stm_op_t op;                          /* Index to enclosing operation */
#endif /* OPERATION_LOGGING != OPLOG_NONE */
};

struct mod_mem_abort_entry {            /* Callback entry */
  void *arg;                            /* Argument to be passed to function */
#if OPERATION_LOGGING != OPLOG_NONE
  stm_op_t op;                          /* Index to enclosing operation */
#endif /* OPERATION_LOGGING != OPLOG_NONE */
};

typedef struct mod_mem_info {
  unsigned short commit_size;           /* Array size for commit callbacks */
  unsigned short commit_nb;             /* Number of commit callbacks */
  struct mod_mem_commit_entry *commit;  /* Commit callback entries */
  unsigned short abort_size;            /* Array size for abort callbacks */
  unsigned short abort_nb;              /* Number of abort callbacks */
  struct mod_mem_abort_entry *abort;    /* Abort callback entries */
} mod_mem_info_t;

/* TODO: to avoid false sharing, this should be in a dedicated cacheline.
 * Unfortunately this will cost one cache line for each module. Probably
 * mod_mem_mem could be included always in mainline stm since allocation is
 * common in transaction (?). */
static struct {
  int key;
} ALIGNED mod_mem = { .key = -1 };

static INLINE void
int_stm_free_commit(const struct stm_tx *tx, const void *arg);

/* ################################################################### *
 * CALLBACKS FUNCTIONS
 * ################################################################### */

static INLINE void
mod_mem_add_on_abort(mod_mem_info_t *icb, void *arg
#if OPERATION_LOGGING != OPLOG_NONE
  , const stm_op_t o
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  ) {
  if (unlikely(icb->abort_nb >= icb->abort_size)) {
    icb->abort_size *= 2;
    icb->abort = xrealloc(icb->abort, sizeof(*icb->abort) * icb->abort_size);
  }
  icb->abort[icb->abort_nb].arg = arg;
#if OPERATION_LOGGING != OPLOG_NONE
  icb->abort[icb->abort_nb].op = o;
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  icb->abort_nb++;
}

static INLINE void
mod_mem_add_on_commit(mod_mem_info_t *icb, const void *arg
#if OPERATION_LOGGING != OPLOG_NONE
  , const stm_op_t o
#endif /* OPERATION_LOGGING != OPLOG_NONE */
) {
  if (unlikely(icb->commit_nb >= icb->commit_size)) {
    icb->commit_size *= 2;
    icb->commit = xrealloc(icb->commit, sizeof(*icb->commit) * icb->commit_size);
  }
  icb->commit[icb->commit_nb].arg = arg;
#if OPERATION_LOGGING != OPLOG_NONE
  icb->commit[icb->commit_nb].op = o;
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  icb->commit_nb++;
}


/* ################################################################### *
 * MEMORY ALLOCATION FUNCTIONS
 * ################################################################### */

static inline void *int_stm_did_malloc(const void *tx, const mod_mem_info_t *icb, const void *addr) {
  for (size_t i = 0; i < icb->abort_nb; ++i) {
    if (icb->abort[i].arg == addr)
      return &icb->abort[i];
  }

  return NULL;
}

static inline struct mod_mem_commit_entry *int_stm_did_free(const mod_mem_info_t *icb, const void *addr) {
  for (size_t i = 0; i < icb->commit_nb; ++i) {
    if (icb->commit[i].arg == addr)
      return &icb->commit[i];
  }

  return NULL;
}

#if OPERATION_LOGGING != OPLOG_NONE
static inline int int_stm_undo_malloc(mod_mem_info_t *icb, struct mod_mem_abort_entry *e) {
  /* Cannot free immediately, because it may have outstanding references that would become incorrect if a new allocation is assigned this memory block */
  assert(e >= icb->abort && e < icb->abort + icb->abort_nb);
  assert(!int_stm_did_free(icb, e));
  /* Use an invalid operation to prevent this memory operation from being subsequently changed/reverted */
  mod_mem_add_on_commit(icb, e->arg, STM_INVALID_OP);
  memmove(e, &icb->abort[icb->abort_nb - 1], sizeof(*e));
  --icb->abort_nb;
  return 1;
}

static inline int int_stm_undo_free(mod_mem_info_t *icb, struct mod_mem_commit_entry *e) {
  assert(e >= icb->commit && e < icb->commit + icb->commit_nb);
  memmove(e, &icb->commit[icb->commit_nb - 1], sizeof(*e));
  --icb->commit_nb;
  return 1;
}

static inline int int_stm_undo_mem_op(struct stm_tx *tx, const stm_op_t o) {
  mod_mem_info_t *icb = NULL;

  if (likely(mod_mem.key) >= 0) {
    icb = (mod_mem_info_t *)int_stm_get_specific(tx, mod_mem.key);
    assert(icb != NULL);
  }

  for (size_t i = 0; i < icb->commit_nb; ++i) {
    if (GET_OP_IDX(icb->commit[i].op.idx) == GET_OP_IDX(o.idx)) {
      int_stm_undo_free(icb, &icb->commit[i]);
      --i;
    }
  }

  for (size_t i = 0; i < icb->abort_nb; ++i) {
    if (GET_OP_IDX(icb->abort[i].op.idx) == GET_OP_IDX(o.idx))
      int_stm_undo_malloc(icb, &icb->abort[i]);
  }

  return 1;
}
#endif /* OPERATION_LOGGING != OPLOG_NONE */

stm_malloc_t stm_did_malloc(const void *addr) {
  TX_GET;

  mod_mem_info_t *icb;

  assert(mod_mem.key >= 0);
  icb = (mod_mem_info_t *)int_stm_get_specific(tx, mod_mem.key);
  assert(icb != NULL);

  struct mod_mem_abort_entry *a = int_stm_did_malloc(tx, icb, addr);
  return a ? MALLOC_FROM_POINTER(icb, a) : STM_INVALID_MALLOC;
}

int stm_undo_malloc(stm_malloc_t e) {
#if OPERATION_LOGGING != OPLOG_NONE
  TX_GET;
  mod_mem_info_t *icb;

  assert(mod_mem.key >= 0);
  icb = (mod_mem_info_t *)int_stm_get_specific(tx, mod_mem.key);
  assert(icb != NULL);

  if (likely(MALLOC_VALID(icb, e)))
    return int_stm_undo_malloc(icb, POINTER_FROM_MALLOC(icb, e));
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  return 0;
}

stm_free_t stm_did_free(const void *addr) {
  mod_mem_info_t *icb;

  assert(mod_mem.key >= 0);
  icb = (mod_mem_info_t *)stm_get_specific(mod_mem.key);
  assert(icb != NULL);

  struct mod_mem_commit_entry *c = int_stm_did_free(icb, addr);
  return c ? FREE_FROM_POINTER(icb, c) : STM_INVALID_FREE;
}

int stm_undo_free(stm_free_t e) {
#if OPERATION_LOGGING != OPLOG_NONE
  mod_mem_info_t *icb;

  assert(mod_mem.key >= 0);
  icb = (mod_mem_info_t *)stm_get_specific(mod_mem.key);
  assert(icb != NULL);

  if (likely(FREE_VALID(icb, e)))
    return int_stm_undo_free(icb, POINTER_FROM_FREE(icb, e));
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  return 0;
}

int stm_undo_mem_op(stm_op_t o) {
#if OPERATION_LOGGING != OPLOG_NONE
  TX_GET;
  return int_stm_undo_mem_op(tx, o);
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  return 0;
}

static INLINE void
int_stm_free_abort(const struct stm_tx *tx, void *arg) {
  xfree(arg);
}

static INLINE void
int_stm_free_commit(const struct stm_tx *tx, const void *arg) {
#if MEMORY_MANAGEMENT == MM_NONE
  xfree(arg);
#elif MEMORY_MANAGEMENT == MM_EPOCH_GC
  /* TODO use tx->end could be also used */
  stm_word_t t = GET_CLOCK;
  gc_free(arg, t);
#endif /* MEMORY_MANAGEMENT */
}

static INLINE void *
int_stm_malloc(struct stm_tx *tx, size_t size)
{
  /* Memory will be freed upon abort */
  mod_mem_info_t *icb;
  void *addr = NULL;

  assert(mod_mem.key >= 0);
  icb = (mod_mem_info_t *)int_stm_get_specific(tx, mod_mem.key);
  assert(icb != NULL);

  /* Round up size */
  if (sizeof(stm_word_t) == 4) {
    size = (size + 3) & ~(size_t)0x03;
  } else {
    size = (size + 7) & ~(size_t)0x07;
  }

  addr = xmalloc(size);

  /* Check for allocator correctness */
  assert(!int_stm_did_free(icb, addr));
  mod_mem_add_on_abort(icb, addr
#if OPERATION_LOGGING != OPLOG_NONE
    , int_stm_get_log(tx)
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  );

  return addr;
}

/*
 * Called by the CURRENT thread to allocate memory within a transaction.
 */
void *stm_malloc(size_t size)
{
  TX_GET;
  return int_stm_malloc(tx, size);
}

void *stm_malloc_tx(struct stm_tx *tx, size_t size)
{
  return int_stm_malloc(tx, size);
}

static inline
void *int_stm_calloc(struct stm_tx *tx, size_t nm, size_t size)
{
  /* Memory will be freed upon abort */
  mod_mem_info_t *icb;
  void *addr = NULL;

  assert(mod_mem.key >= 0);
  icb = (mod_mem_info_t *)int_stm_get_specific(tx, mod_mem.key);
  assert(icb != NULL);

  /* Round up size */
  if (sizeof(stm_word_t) == 4) {
    size = (size + 3) & ~(size_t)0x03;
  } else {
    size = (size + 7) & ~(size_t)0x07;
  }

  addr = xcalloc(nm, size);

  /* Check for allocator correctness */
  assert(!int_stm_did_free(icb, addr));
  mod_mem_add_on_abort(icb, addr
#if OPERATION_LOGGING != OPLOG_NONE
    , int_stm_get_log(tx)
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  );

  return addr;
}

/*
 * Called by the CURRENT thread to allocate initialized memory within a transaction.
 */
void *stm_calloc(size_t nm, size_t size)
{
  TX_GET;
  return int_stm_calloc(tx, nm, size);
}

void *stm_calloc_tx(struct stm_tx *tx, size_t nm, size_t size)
{
  return int_stm_calloc(tx, nm, size);
}

static inline
void int_stm_free2(struct stm_tx *tx, void *addr, size_t idx, size_t size)
{
  /* Memory disposal is delayed until commit */
  mod_mem_info_t *icb;

  assert(mod_mem.key >= 0);
  icb = (mod_mem_info_t *)int_stm_get_specific(tx, mod_mem.key);
  assert(icb != NULL);

  /* TODO: if block allocated in same transaction => no need to overwrite */
  if (!tx->attr.no_overwrite && size > 0) {
    stm_word_t *a;
    /* Overwrite to prevent inconsistent reads */
    if (sizeof(stm_word_t) == 4) {
      idx = (idx + 3) >> 2;
      size = (size + 3) >> 2;
    } else {
      idx = (idx + 7) >> 3;
      size = (size + 7) >> 3;
    }
    a = (stm_word_t *)addr + idx;
    while (size-- > 0) {
      /* Acquire lock and update version number */
#  if DETECTION == TIME_BASED
      int_stm_store2(tx, a++, 0, 0);
#  endif /* DETECTION */
    }
  }

  /* Check for double free */
  assert(!int_stm_did_free(icb, addr));
  /* Schedule for removal */
  mod_mem_add_on_commit(icb, addr
#if OPERATION_LOGGING != OPLOG_NONE
    , int_stm_get_log(tx)
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  );
}

/*
 * Called by the CURRENT thread to free memory within a transaction.
 */
void stm_free2(void *addr, size_t idx, size_t size)
{
  TX_GET;
  int_stm_free2(tx, addr, idx, size);
}

void stm_free2_tx(struct stm_tx *tx, void *addr, size_t idx, size_t size)
{
  int_stm_free2(tx, addr, idx, size);
}

/*
 * Called by the CURRENT thread to free memory within a transaction.
 */
void stm_free(void *addr, size_t size)
{
  TX_GET;
  int_stm_free2(tx, addr, 0, size);
}

void stm_free_tx(struct stm_tx *tx, void *addr, size_t size)
{
  int_stm_free2(tx, addr, 0, size);
}


/*
 * Called upon transaction commit.
 */
static void mod_mem_on_commit(const struct stm_tx *tx, const void *arg)
{
  mod_mem_info_t *icb = (mod_mem_info_t *)int_stm_get_specific(tx, mod_mem.key);
  assert(icb != NULL);

  /* Call commit callback */
  while (icb->commit_nb > 0) {
    int_stm_free_commit(tx, icb->commit[--icb->commit_nb].arg);
  }

  /* Reset abort callback */
  icb->abort_nb = 0;
}

/*
 * Called upon transaction abort.
 */
static void mod_mem_on_abort(const struct stm_tx *tx, const stm_tx_abort_t reason, const void *arg)
{
  mod_mem_info_t *icb = (mod_mem_info_t *)int_stm_get_specific(tx, mod_mem.key);
  assert(icb != NULL);

  /* Call abort callback */
  while (icb->abort_nb > 0) {
    int_stm_free_abort(tx, icb->abort[--icb->abort_nb].arg);
  }

  /* Reset commit callback */
  icb->commit_nb = 0;
}

/*
 * Called upon thread creation.
 */
static void mod_mem_on_thread_init(struct stm_tx *tx, const void *arg)
{
  mod_mem_info_t *icb;

  icb = (mod_mem_info_t *)xmalloc(sizeof(mod_mem_info_t));
  icb->commit_nb = icb->abort_nb = 0;
  icb->commit_size = icb->abort_size = DEFAULT_CB_SIZE;
  icb->commit = xmalloc(sizeof(*icb->commit) * icb->commit_size);
  icb->abort = xmalloc(sizeof(*icb->abort) * icb->abort_size);
  int_stm_set_specific(tx, mod_mem.key, icb);
}

/*
 * Called upon thread deletion.
 */
static void mod_mem_on_thread_exit(const struct stm_tx *tx, const void *arg)
{
  mod_mem_info_t *icb;

  icb = (mod_mem_info_t *)int_stm_get_specific(tx, mod_mem.key);
  assert(icb != NULL);

  xfree(icb->abort);
  xfree(icb->commit);
  xfree(icb);
}

/*
 * Initialize module.
 */
void
mod_mem_init(void)
{
  /* Module is already initialized? */
  if (mod_mem.key >= 0)
    return;

  if (!stm_register(mod_mem_on_thread_init, mod_mem_on_thread_exit, NULL, NULL, mod_mem_on_commit, mod_mem_on_abort, NULL)) {
    fprintf(stderr, "Cannot register callbacks\n");
    exit(1);
  }
  mod_mem.key = stm_create_specific();
  if (mod_mem.key < 0) {
    fprintf(stderr, "Cannot create specific key\n");
    exit(1);
  }
}
