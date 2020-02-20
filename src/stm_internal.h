/*
 * File:
 *   stm_internal.h
 * Author(s):
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * Description:
 *   STM internal functions.
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

#ifndef _STM_INTERNAL_H_
#define _STM_INTERNAL_H_

#include <pthread.h>
#include <assert.h>
#if CM == CM_MERGE
#include <stdarg.h>
#endif /* CM == CM_MERGE */
#include <string.h>
#include <stm.h>

#include "tls.h"
#include "utils.h"
#include "atomic.h"
#include "gc.h"

#if CM == CM_MERGE
# include "mod_mem.h"
#endif /* CM == CM_MERGE */

#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE || WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE || WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
# ifdef __SSE4_2__
#  include <smmintrin.h>
# else
#  warning "Falling back to XOR-based hash function!"
# endif /* __SSE4_2__ */

#include "khash.h"
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE || WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE || WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */

#if defined(DEBUG_ABORT)
#include "../../libtardis/include/debug_dwarf.h"
static debug_t *debug = NULL;
static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
#endif /* defined(DEBUG_ABORT) */

/* ################################################################### *
 * DEFINES
 * ################################################################### */


/* Conflict detection */
#define TIME_BASED                      0

#ifndef DETECTION
# define DETECTION                      TIME_BASED
#endif /* ! DETECTION */

/* Designs */
#define WRITE_BACK_ETL                  0
#define WRITE_BACK_ETL_VR               1
#define WRITE_BACK_CTL                  2
#define WRITE_THROUGH                   3
#define MODULAR                         4

#ifndef DESIGN
# define DESIGN                         WRITE_BACK_ETL
#endif /* ! DESIGN */

/* Contention managers */
#define CM_RESTART                      0
#define CM_AGGRESSIVE                   1
#define CM_DELAY                        2
#define CM_TIMESTAMP                    3
#define CM_BACKOFF                      4
#define CM_KARMA                        5
#define CM_MERGE                        6

#ifndef CM
# define CM                             CM_RESTART
#endif /* ! CM */

/* Memory management */
#define MM_NONE                         0
#define MM_EPOCH_GC                     1

#ifndef MEMORY_MANAGEMENT
# define MEMORY_MANAGEMENT              MM_NONE
#endif /* ! MEMORY_MANAGEMENT */

/* Read/write set lookups */
#define RW_ARRAY                        0
#define RW_HASH_TABLE                   1
#define RW_ADAPTIVE                     2

#ifndef READ_SET
# define READ_SET                       RW_ARRAY
#endif /* ! READ_SET */
#ifndef WRITE_SET
# define WRITE_SET                      RW_ARRAY
#endif /* ! WRITE_SET */
#ifndef WRITE_SET_UNIQUE
# define WRITE_SET_UNIQUE               RW_ARRAY
#endif /* ! WRITE_SET_UNIQUE */

/* Operation logging */
#ifndef OPERATION_LOGGING
# define OPERATION_LOGGING              OPLOG_NONE
#endif /* ! OPERATION_LOGGING */
#define OPLOG_NONE                      0
#define OPLOG_FULL                      1

/* Laziness */
#define LZ_ZERO                         0
#define LZ_MERGE                        1

#ifndef LAZINESS
# define LAZINESS                       LZ_ZERO
#endif /* ! LAZINESS */

#if CM == CM_AGGRESSIVE && ! defined(TRANSACTION_OPERATIONS)
# error "AGGRESSIVE contention manager requires TRANSACTION_OPERATIONS"
#endif

#if CM == CM_DELAY && ! defined(CONTENDED_LOCK_TRACKING)
# error "DELAY contention manager requires CONTENDED_LOCK_TRACKING"
#endif

#if CM == CM_TIMESTAMP && ! defined (CONFLICT_TRACKING)
# error "TIMESTAMP contention manager requires CONFLICT_TRACKING"
#endif

#if CM == CM_KARMA && ! defined(CONFLICT_TRACKING)
# error "KARMA contention manager requires CONFLICT_TRACKING"
#endif

#if CM == CM_MERGE && DESIGN != WRITE_BACK_CTL
# error "CM_MERGE is only supported for WRITE_BACK_CTL"
#endif

#if OPERATION_LOGGING == OPLOG_FULL && ! defined(READ_SET_SOURCE)
# error "OPERATION_LOGGING requires READ_SET_SOURCE"
#endif /* OPERATION_LOGGING == OPLOG_FULL && ! READ_SET_SOURCE */

#if CM == CM_MERGE && OPERATION_LOGGING == OPLOG_NONE
# error "MERGE contention manager requires OPERATION_LOGGING != OPLOG_NONE"
#endif /* CM == CM_MERGE && OPERATION_LOGGING == OPLOG_NONE */

#if CM == CM_MERGE && DETECTION == TIME_BASED && ! defined(READ_SET_DETAILED)
# error "MERGE contention manager requires READ_SET_DETAILED with TIME_BASED conflict detection"
#endif /* CM == CM_MERGE && DETECTION == TIME_BASED && ! READ_SET_DETAILED */

#if CM == CM_MERGE && OPERATION_LOGGING == OPLOG_FULL && ! defined(READ_SET_ORDERED)
# error "MERGE contention manager requires READ_SET_ORDERED if OPERATION_LOGGING is OPLOG_FULL"
#endif /* CM == CM_MERGE && OPERATION_LOGGING != OPLOG_NONE && ! READ_SET_ORDERED */

#if CM == CM_MERGE && MEMORY_MANAGEMENT != MM_EPOCH_GC
# error "MERGE contention manager requires MEMORY_MANAGEMENT == MM_EPOCH_GC"
#endif /* CM == CM_MERGE && MEMORY_MANAGED != MM_EPOCH_GC */

#if defined(CONFLICT_TRACKING) && MEMORY_MANAGEMENT == MM_NONE
# error "CONFLICT_TRACKING requires MEMORY_MANAGEMENT != MM_NONE"
#endif /* defined(CONFLICT_TRACKING) && MEMORY_MANAGEMENT == MM_NONE */

#if defined(READ_LOCKED_DATA) && DESIGN != WRITE_BACK_ETL
# error "READ_LOCKED_DATA can only be used with WRITE_BACK_ETL design"
#endif /* defined(READ_LOCKED_DATA) && DESIGN != WRITE_BACK_ETL */

#if MEMORY_MANAGEMENT != MM_NONE && defined(SIGNAL_HANDLER)
# error "SIGNAL_HANDLER can only be used with MEMORY_MANAGEMENT == MM_NONE"
#endif /* MEMORY_MANAGEMENT != MM_NONE && defined(SIGNAL_HANDLER) */

#if defined(TRANSACTION_OPERATIONS) && ! defined(CONFLICT_TRACKING)
# error "TRANSACTION_OPERATIONS requires CONFLICT_TRACKING"
#endif /* defined(TRANSACTION_OPERATIONS) && ! defined(CONFLICT_TRACKING) */

#if LAZINESS == LZ_MERGE && (CM != CM_MERGE || OPERATION_LOGGING != OPLOG_FULL)
# error "LZ_MERGE requires CM_MERGE and OPLOG_FULL"
#endif /* LAZINESS == LZ_MERGE && (CM != CM_MERGE || OPERATION_LOGGING != OPLOG_FULL) */

#define TX_GET                          stm_tx_t *tx = tls_get_tx()

#define DEFAULT_CB_SIZE                 16                  /* Initial size of callbacks for dynamic memory */

#ifndef R_SET_SIZE
# define R_SET_SIZE                     8192                /* Initial size of read set */
#endif /* ! R_SET_SIZE */
#ifndef W_SET_SIZE
# define W_SET_SIZE                     1024                /* Initial size of write set */
#endif /* ! W_SET_SIZE */
#ifndef W_SET_UNIQUE_SIZE
# define W_SET_UNIQUE_SIZE              1024                /* Initial size of write set unique */
#endif /* ! W_SET_SIZE */

#ifndef RW_ADAPTIVE_THRESHOLD
# define RW_ADAPTIVE_THRESHOLD          64                  /* Threshold between array and hash table */
#endif /* ! RW_ADAPTIVE_THRESHOLD */

#if OPERATION_LOGGING != OPLOG_NONE
# ifndef OP_LOG_SIZE
#  define OP_LOG_SIZE                   65536               /* Initial size of operation log */
# endif /* ! OP_LOG_SIZE */
# define OP_NAME_SIZE                   16                  /* Maximum length of operation string */
# define OP_INFO_SIZE                   32                  /* Initial size of operation table */
#endif /* OPERATION_LOGGING != OPLOG_NONE */

#ifndef LOCK_ARRAY_LOG_SIZE
# define LOCK_ARRAY_LOG_SIZE            20                  /* Size of lock array: 2^20 = 1M */
#endif /* LOCK_ARRAY_LOG_SIZE */

#ifndef LOCK_SHIFT_EXTRA
# define LOCK_SHIFT_EXTRA               2UL                 /* 2 extra shift */
#endif /* LOCK_SHIFT_EXTRA */

#if CM == CM_BACKOFF
# ifndef MIN_BACKOFF
#  define MIN_BACKOFF                   (1UL << 2)
# endif /* MIN_BACKOFF */
# ifndef MAX_BACKOFF
#  define MAX_BACKOFF                   (1UL << 31)
# endif /* MAX_BACKOFF */
#endif /* CM == CM_BACKOFF */

#if DESIGN == WRITE_BACK_ETL_VR
# define VR_THRESHOLD                   "VR_THRESHOLD"
# ifndef VR_THRESHOLD_DEFAULT
#  define VR_THRESHOLD_DEFAULT          3                   /* -1 means no visible reads. 0 means always use visible reads. */
# endif /* VR_THRESHOLD_DEFAULT */
#endif /* DESIGN == WRITE_BACK_ETL_VR */

#define NO_SIGNAL_HANDLER               "NO_SIGNAL_HANDLER"

#if defined(CTX_LONGJMP)
# define JMP_BUF                        jmp_buf
# define LONGJMP(ctx, value)            longjmp(ctx, value)
#elif defined(CTX_ITM)
/* TODO adjust size to real size. */
# define JMP_BUF                        jmp_buf
# define LONGJMP(ctx, value)            CTX_ITM(value, ctx)
#else /* !CTX_LONGJMP && !CTX_ITM */
# define JMP_BUF                        sigjmp_buf
# define LONGJMP(ctx, value)            siglongjmp(ctx, value)
#endif /* !CTX_LONGJMP && !CTX_ITM */

/* ################################################################### *
 * TYPES
 * ################################################################### */

typedef enum {                                /* Transaction status */
  TX_IDLE = 0UL,
  TX_ACTIVE_BIT = 1UL,                        /* Lowest bit indicates activity */
  TX_COMMITTED = (1UL << 1),
  TX_ABORTED = (2UL << 1),
  TX_KILLED = (3UL << 1),
  TX_COMMITTING = TX_COMMITTED | TX_ACTIVE_BIT,
  TX_ABORTING = TX_ABORTED | TX_ACTIVE_BIT,
  TX_KILLING = TX_KILLED | TX_ACTIVE_BIT,
  TX_IRREVOCABLE = (1UL << 3) | TX_ACTIVE_BIT /* Fourth bit indicates irrevocability */
} tx_status_t;
#define STATUS_BITS                     4UL
#define STATUS_MASK                     ((1UL << STATUS_BITS) - 1)

#ifdef TRANSACTION_OPERATIONS
# define SET_STATUS(s, v)               ATOMIC_STORE_REL(&(s), ((s) & ~(stm_word_t)STATUS_MASK) | (v))
# define INC_STATUS_COUNTER(s)          ((((s) >> STATUS_BITS) + 1) << STATUS_BITS)
# define UPDATE_STATUS_RAW(s, v)        ATOMIC_STORE_REL(&(s), INC_STATUS_COUNTER(s) | (v))
# define UPDATE_STATUS(s, os, v)        ATOMIC_CAS_FULL(&(s), os, INC_STATUS_COUNTER(os) | (v))
# define GET_STATUS(s)                  ((s) & STATUS_MASK)
# define GET_STATUS_COUNTER(s)          ((s) >> STATUS_BITS)
#else /* TRANSACTION_OPERATIONS */
# define SET_STATUS(s, v)               ((s) = (v))
# define UPDATE_STATUS_RAW(s, v)        ((s) = (v))
# define UPDATE_STATUS(s, os, v)        UPDATE_STATUS_RAW(s, v)
# define GET_STATUS(s)                  ((s))
#endif /* TRANSACTION_OPERATIONS */
#define IS_ACTIVE(s)                    ((GET_STATUS(s) & TX_ACTIVE_BIT) == TX_ACTIVE_BIT)

/* ################################################################### *
 * LOCKS
 * ################################################################### */

/*
 * A lock is a unsigned integer of the size of a pointer.
 * The LSB is the lock bit. If it is set, this means:
 * - At least some covered memory addresses is being written.
 * - All bits of the lock apart from the lock bit form
 *   a pointer that points to the write log entry holding the new
 *   value. Multiple values covered by the same log entry and orginized
 *   in a linked list in the write log.
 * If the lock bit is not set, then:
 * - All covered memory addresses contain consistent values.
 * - All bits of the lock besides the lock bit contain a version number
 *   (timestamp).
 *   - The high order bits contain the commit time.
 *   - The low order bits contain an incarnation number (incremented
 *     upon abort while writing the covered memory addresses).
 * When visible reads are enabled, two bits are used as read and write
 * locks. A read-locked address can be read by an invisible reader.
 */

#ifdef TRANSACTION_OPERATIONS
# define OWNED_BITS                     2UL                 /* 2 bits */
# define WRITE_MASK                     0x01UL              /* 1 bit */
# define READ_MASK                      0x02UL              /* 1 bit */
# define OWNED_MASK                     (WRITE_MASK | READ_MASK)
#else /* TRANSACTION_OPERATIONS */
# define OWNED_BITS                     1UL                 /* 1 bit */
# define WRITE_MASK                     0x01UL              /* 1 bit */
# define OWNED_MASK                     (WRITE_MASK)
#endif /* TRANSACTION_OPERATIONS */
#if DESIGN == WRITE_THROUGH
# define INCARNATION_BITS               3UL                 /* 3 bits */
# define INCARNATION_MAX                ((1UL << INCARNATION_BITS) - 1)
# define INCARNATION_MASK               (INCARNATION_MAX << 1)
# define LOCK_BITS                      (OWNED_BITS + INCARNATION_BITS)
#else
# define LOCK_BITS                      (OWNED_BITS)
#endif /* DESIGN == WRITE_THROUGH */
#define MAX_THREADS                     8192                /* Upper bound (large enough) */
#define VERSION_MAX                     ((~(stm_word_t)0 >> LOCK_BITS) - MAX_THREADS)

/*
 * We use an array of locks and hash the address to find the location of the lock.
 * We try to avoid collisions as much as possible (two addresses covered by the same lock).
 */
#define LOCK_READ(l)                    (ATOMIC_LOAD(&l->contents))
#define LOCK_READ_ACQ(l)                (ATOMIC_LOAD_ACQ(&l->contents))
#define LOCK_WRITE(l, t)                (ATOMIC_STORE(&l->contents, t))
#define LOCK_WRITE_REL(l, t)            (ATOMIC_STORE_REL(&l->contents, t))
#define LOCK_WRITE_CAS(l, v, t)         (ATOMIC_CAS_FULL(&l->contents, v, t))

typedef stm_word_t stm_version_t;

typedef struct {
  stm_version_t contents;
} stm_lock_t;

#if DETECTION == TIME_BASED
# define LOCK_ARRAY_SIZE                (1UL << LOCK_ARRAY_LOG_SIZE)

# define LOCK_MASK                      (LOCK_ARRAY_SIZE - 1)
# define LOCK_SHIFT                     (((sizeof(stm_word_t) == 4) ? 2 : 3) + LOCK_SHIFT_EXTRA)
# define LOCK_IDX(a)                    (((stm_word_t)(a) >> LOCK_SHIFT) & LOCK_MASK)
# ifdef LOCK_IDX_SWAP
#  if LOCK_ARRAY_LOG_SIZE < 16
#   error "LOCK_IDX_SWAP requires LOCK_ RRAY_LOG_SIZE to be at least 16"
#  endif /* LOCK_ARRAY_LOG_SIZE < 16 */
#  define GET_LOCK(a)                   (_tinystm.locks + lock_idx_swap(LOCK_IDX(a)))
# else /* ! LOCK_IDX_SWAP */
#  define GET_LOCK(a)                   (_tinystm.locks + LOCK_IDX(a))
# endif /* ! LOCK_IDX_SWAP */

# define LOCK_GET_OWNED(a, l)           (l & OWNED_MASK)
# define LOCK_GET_WRITE(a, l)           (l & WRITE_MASK)
# define LOCK_SET_ADDR_WRITE(v, l)      ((stm_word_t)(v) | WRITE_MASK)    /* WRITE bit set */
# define LOCK_GET_ADDR(l)               (l & ~(stm_word_t)OWNED_MASK)
# if TRANSACTION_OPERATIONS
#  define LOCK_GET_READ(l)              (l & READ_MASK)
#  define LOCK_SET_ADDR_READ(a)         (a | READ_MASK)     /* READ bit set */
#  define LOCK_UPGRADE(l)               (l | WRITE_MASK)
# endif /* TRANSACTION_OPERATIONS */
# define LOCK_GET_TIMESTAMP(l)          (l >> (LOCK_BITS))
# define LOCK_SET_TIMESTAMP(w, t, l)    (t << (LOCK_BITS))
# if DESIGN == WRITE_THROUGH
#  define LOCK_GET_INCARNATION(l)       ((l & INCARNATION_MASK) >> OWNED_BITS)
#  define LOCK_SET_INCARNATION(i)       (i << OWNED_BITS)   /* OWNED bit not set */
#  define LOCK_UPD_INCARNATION(l, i)    ((l & ~(stm_word_t)(INCARNATION_MASK | OWNED_MASK)) |  LOCK_SET_INCARNATION(i))
# endif /* DESIGN == WRITE_THROUGH */
# ifdef UNIT_TX
#  define LOCK_UNIT                     (~(stm_word_t)0)
# endif /* UNIT_TX */
#endif /* DETECTION == TIME_BASED */

/*
 * We use the very same hash functions as TL2 for degenerate Bloom
 * filters on 32 bits.
 */
#ifdef USE_BLOOM_FILTER
# define FILTER_HASH(a)                 (((stm_word_t)a >> 2) ^ ((stm_word_t)a >> 5))
# define FILTER_BITS(a)                 (1UL << (FILTER_HASH(a) & 0x1F))
#endif /* USE_BLOOM_FILTER */

typedef struct { unsigned int idx; } stm_write_unique_t;

/* Use index-based references to allow resize of underlying array */
#define STM_INVALID_WRITE_UNIQUE        ((stm_write_unique_t){ .idx = STM_BAD_IDX })

#define READ_FROM_POINTER(tx, r)        ((stm_read_t){ .idx = (r) - tx->r_set.entries })
#define WRITE_FROM_POINTER(tx, w)       ((stm_write_t){ .idx = (w) - tx->w_set.entries })
#define WRITE_UNIQUE_FROM_POINTER(tx, wu) ((stm_write_unique_t){ .idx = (wu) - tx->w_set_unique.entries })
#define POINTER_FROM_READ(tx, r)        (__builtin_types_compatible_p(typeof(r), stm_read_t) ? tx->r_set.entries + (r).idx : NULL)
#define POINTER_FROM_WRITE(tx, w)       (__builtin_types_compatible_p(typeof(w), stm_write_t) ? tx->w_set.entries + (w).idx : NULL)
#define POINTER_FROM_WRITE_UNIQUE(tx, wu) (__builtin_types_compatible_p(typeof(wu), stm_write_unique_t) ? tx->w_set_unique.entries + (wu).idx : NULL)
#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
# define READ_VALID(tx, r)              (__builtin_types_compatible_p(typeof(r), stm_read_t) && (r).idx > READ_RESERVED_IDX && (r).idx < tx->r_set.nb_entries)
# define READ_VALID_FAST(tx, r)         (__builtin_types_compatible_p(typeof(r), stm_read_t) && (r).idx < tx->r_set.nb_entries)
# define READ_POINTER_VALID(tx, r)      ((r) >= tx->r_set.entries + READ_RESERVED_IDX + 1 && (r) < tx->r_set.entries + tx->r_set.nb_entries)
#else
# define READ_VALID(tx, r)              (__builtin_types_compatible_p(typeof(r), stm_read_t) && (r).idx < tx->r_set.nb_entries)
# define READ_VALID_FAST(tx, r)         READ_VALID(tx, r)
# define READ_POINTER_VALID(tx, r)      ((r) >= tx->r_set.entries && (r) < tx->r_set.entries + tx->r_set.nb_entries)
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE || WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
# define WRITE_VALID(tx, w)             (__builtin_types_compatible_p(typeof(w), stm_write_t) && (w).idx > WRITE_RESERVED_IDX && (w).idx < tx->w_set.nb_entries)
# define WRITE_VALID_FAST(tx, w)        (__builtin_types_compatible_p(typeof(w), stm_write_t) && (w).idx < tx->w_set.nb_entries)
# define WRITE_POINTER_VALID(tx, w)     ((w) >= tx->w_set.entries + WRITE_RESERVED_IDX + 1 && (w) < tx->w_set.entries + tx->w_set.nb_entries)
# define WRITE_UNIQUE_VALID(tx, wu)     (__builtin_types_compatible_p(typeof(wu), stm_write_unique_t) && (wu).idx > WRITE_RESERVED_IDX && (wu).idx < tx->w_set_unique.nb_entries)
# define WRITE_UNIQUE_VALID_FAST(tx, wu) (__builtin_types_compatible_p(typeof(wu), stm_write_unique_t) && (wu).idx < tx->w_set_unique.nb_entries)
# define WRITE_UNIQUE_POINTER_VALID(tx, wu) ((wu) >= tx->w_set_unique.entries + WRITE_RESERVED_IDX + 1 && (wu) < tx->w_set_unique.entries + tx->w_set_unique.nb_entries)
#else
# define WRITE_VALID(tx, w)             (__builtin_types_compatible_p(typeof(w), stm_write_t) && (w).idx < tx->w_set.nb_entries)
# define WRITE_VALID_FAST(tx, w)        WRITE_VALID(tx, w)
# define WRITE_POINTER_VALID(tx, w)     ((w) >= tx->w_set.entries && (w) < tx->w_set.entries + tx->w_set.nb_entries)
# define WRITE_UNIQUE_VALID(tx, wu)     (__builtin_types_compatible_p(typeof(wu), stm_write_unique_t) && (wu).idx < tx->w_set_unique.nb_entries)
# define WRITE_UNIQUE_VALID_FAST(tx, wu) WRITE_UNIQUE_VALID(tx, wu)
# define WRITE_UNIQUE_POINTER_VALID(tx, wu) ((wu) >= tx->w_set_unique.entries && (wu) < tx->w_set_unique.entries + tx->w_set_unique.nb_entries)
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE || WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */

#if OPERATION_LOGGING != OPLOG_NONE
# if OPERATION_LOGGING == OPLOG_FULL
#  define GET_OP_IDX(o)                 (o)
#  define GET_LOG_ENTRY(tx, idx)        ((op_entry_t *)(tx->op_log.entries + (idx)))
#  define OP_ENTRY_SIZE(id)             (__builtin_types_compatible_p(typeof(id), stm_op_id_t) ? (sizeof(op_entry_t) + (_tinystm.op_info.ids[(id).idx].fi.nargs + (_tinystm.op_info.ids[(id).idx].fi.rtype->type != FFI_TYPE_VOID ? 1 : 0)) * sizeof(stm_union_t) + (_tinystm.op_info.ids[(id).idx].fi.rtype->type == FFI_TYPE_STRUCT ? _tinystm.op_info.ids[(id).idx].fi.rtype->size : 0)) : 0)
                                                            /* Log entry size = Base log entry size + (number of arguments + return value) * argument union size + struct return value size */
#  define OP_VALID(tx, o)               (__builtin_types_compatible_p(typeof(o), stm_op_t) && (o).idx < tx->op_log.used)
# endif /* OPERATION_LOGGING */

# define OPID_VALID(e)                  (__builtin_types_compatible_p(typeof(e), stm_op_id_t) && (e).idx < _tinystm.op_info.size)

# define OP_SUBTREE(s, o)               (__builtin_types_compatible_p(typeof(o), stm_op_t) && GET_LOG_ENTRY(tx, (o).idx)->parent.idx >= (s))
#endif /* OPERATION_LOGGING != OPLOG_NONE */

#define ENTRY_FROM_READ_POINTER(tx, r)  ((entry_t)((r) - tx->r_set.entries))
#define ENTRY_FROM_WRITE_POINTER(tx, w) ((entry_t)((w) - tx->w_set.entries))
#define ENTRY_FROM_WRITE(tx, w)         ((entry_t)(w.idx))

#define ALIGN_ADDR(a)                   ((stm_word_t *)((uintptr_t)(a) & ~(sizeof(stm_word_t) - 1)))

/* ################################################################### *
 * CLOCK
 * ################################################################### */

/* At least twice a cache line (not required if properly aligned and padded) */
#define CLOCK                           (_tinystm.gclock)

#define GET_CLOCK                       (ATOMIC_LOAD_ACQ(&CLOCK))
#if DETECTION == TIME_BASED
# define FETCH_INC_CLOCK                (ATOMIC_FETCH_INC_FULL(&CLOCK))
#endif /* DETECTION */

/* ################################################################### *
 * CALLBACKS
 * ################################################################### */

/* The number of 7 is chosen to make fit the number and the array in a
 * same cacheline (assuming 64bytes cacheline and 64bits CPU). */
#define MAX_CB                          7

/* Declare as static arrays (vs. lists) to improve cache locality */
/* The number transaction local specific for modules. */
#ifndef MAX_SPECIFIC
# define MAX_SPECIFIC                   7
#endif /* MAX_SPECIFIC */

struct stm_tx;

#if OPERATION_LOGGING != OPLOG_NONE
# if OPERATION_LOGGING == OPLOG_FULL
typedef enum op_entry_status {
  OP_STATUS_STARTED,                    /* Operation has started and is still on stack */
  OP_STATUS_FINISHED,                   /* Operation has finished and is not on stack */
  OP_STATUS_REVERTED,                   /* Operation has finished and was reverted */
} op_entry_status_t;
# endif /* OPERATION_LOGGING == OPLOG_FULL */

typedef struct op_entry {
  stm_op_id_t id;                       /* User-defined operation ID */
  stm_op_t parent;                      /* Index of parent operation (nested) */
#  if CM == CM_MERGE
#   ifdef MERGE_JIT
  stm_merge_cb_t jit;                   /* JIT merge function */
#   endif /* MERGE_JIT */
#  endif /* CM == CM_MERGE */
# if OPERATION_LOGGING == OPLOG_FULL
  op_entry_status_t status;             /* Status of this log entry */
  stm_read_t reads;                     /* Read set entries */
# endif /* OPERATION_LOGGING == OPLOG_FULL */
# if OPERATION_LOGGING == OPLOG_FULL
  stm_union_t args[];                   /* Variable-length arguments and optional return value. If the return value is a struct, it is stored immediately after args[return value], and args[return value].ptr is set to this buffer */
# endif /* OPERATION_LOGGING == OPLOG_FULL */
} op_entry_t;

/* Used as a special wildcard operation to find the most recent write from any for the address */
# define STM_SPECIAL_OP                 ((stm_op_t){ .idx = (unsigned int)-1 })
#endif /* OPERATION_LOGGING != OPLOG_NONE */

#if OPERATION_LOGGING != OPLOG_NONE
typedef struct op_log {
  unsigned char *entries;               /* Array of entries (actually of op_entry_t type) */
  unsigned int used;                    /* Used space (in bytes) */
  unsigned int size;                    /* Size of array (in bytes) */
} op_log_t;
#endif /* OPERATION_LOGGING != OPLOG_NONE */

#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
#define READ_RESERVED_IDX               0
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */

#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE || WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
#define WRITE_RESERVED_IDX              0
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */

typedef struct r_entry {                /* Read set entry */
#ifdef READ_SET_SOURCE
  stm_write_t source;                   /* Source of this read: write set or memory */
#endif /* READ_SET_SOURCE */
#if DETECTION == TIME_BASED
  const stm_lock_t *lock;               /* Pointer to lock (for fast access) */
  stm_version_t version;                /* Version read */
#endif /* DETECTION == TIME_BASED */
#ifdef READ_SET_DETAILED
  const stm_word_t *addr;               /* Address read */
  stm_word_t value;                     /* Value read */
#endif /* READ_SET_DETAILED */
#if OPERATION_LOGGING != OPLOG_NONE
  stm_op_t op;                          /* Index to enclosing operation */
#endif /* OPERATION_LOGGING != OPLOG_NONE */
#ifdef READ_SET_ORDERED
  stm_read_t next;                      /* Linked list of entries */
#endif /* READ_SET_ORDERED */
#ifdef READ_SET_TAGGED
  uintptr_t tag;                        /* Tag value */
#endif /* READ_SET_TAGGED */
} r_entry_t;

#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
static khint_t kh_read_hash(const stm_read_t rt);
static khint_t kh_read_equal(const stm_read_t a, const stm_read_t b);

/* Initialize the hash set of stm_read_t type */
KHASH_INIT(r_set, stm_read_t, char, 0, kh_read_hash, kh_read_equal);
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */

typedef struct r_set {                  /* Read set */
  r_entry_t *entries;                   /* Array of entries */
#ifdef READ_SET_ORDERED
  stm_read_t head;                      /* Head of the ordered linked list of entries */
  stm_read_t tail;                      /* Tail of the ordered linked list of entries */
  stm_read_t free;                      /* Free list of entries */
#endif /* READ_SET_ORDERED */
  unsigned int nb_entries;              /* Number of entries */
  unsigned int size;                    /* Size of array */
#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
  khash_t(r_set) *hash;                 /* Hash table */
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
} r_set_t;

struct w_entry_unique;

typedef struct w_entry {                /* Write set entry */
  stm_word_t value;                     /* New (write-back) or old (write-through) value */
#ifdef READ_SET_SOURCE
  stm_version_t version;                /* Update timestamp, used by CM_MERGE */
#endif /* READ_SET_SOURCE */
  stm_word_t mask;                      /* Write mask */
#if OPERATION_LOGGING == OPLOG_FULL
  stm_op_t op;                          /* Index to enclosing operation */
#endif /* OPERATION_LOGGING == OPLOG_FULL */
#if OPERATION_LOGGING == OPLOG_FULL
  stm_op_t op_next;                     /* Index of the next operation */
  stm_write_t addr_prev;                /* Previous write entry for this address (if any) */
                                        // FIXME: Sorted doubly linked list?
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  stm_write_unique_t unique;            /* Parent unique write */
} w_entry_t;

#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
static khint_t kh_write_hash(const stm_write_t k);
static khint_t kh_write_equal(const stm_write_t a, const stm_write_t b);

/* Initialize the hash set of stm_write_t type */
KHASH_INIT(w_set, stm_write_t, char, 0, kh_write_hash, kh_write_equal);
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */

typedef struct w_set {                  /* Write set */
  w_entry_t *entries;                   /* Array of entries */
  unsigned int nb_entries;              /* Number of entries */
  unsigned int size;                    /* Size of array */
#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
  khash_t(w_set) *hash;                 /* Hash table */
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */
} w_set_t;

typedef struct w_entry_unique {         /* Unique write set */
#if DETECTION == TIME_BASED
    const stm_lock_t *lock;             /* Pointer to lock (for fast access) */
#endif /* DETECTION == TIME_BASED */
    stm_word_t *addr;                   /* Address */
    stm_write_t latest;                 /* Latest write for this address */
#if DETECTION == TIME_BASED
    stm_version_t version;            /* Version overwritten */
#endif /* DETECTION == TIME_BASED */
#ifdef CONFLICT_TRACKING
    struct stm_tx *tx;                  /* Transaction owning the write set */
#endif /* CONFLICT_TRACKING */
    union {
      stm_write_unique_t next;          /* WRITE_BACK_ETL || WRITE_THROUGH: Next address covered by same lock (if any) */
      stm_word_t no_drop;               /* WRITE_BACK_CTL: Should we drop lock upon abort? */
    };
} ALIGNED w_entry_unique_t;

#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
static khint_t kh_write_unique_hash(const stm_write_unique_t k);
static khint_t kh_write_unique_equal(const stm_write_unique_t a, const stm_write_unique_t b);

/* Initialize the hash set of w_set_unique_t * type */
KHASH_INIT(w_set_unique, stm_write_unique_t, char, 0, kh_write_unique_hash, kh_write_unique_equal);
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */

typedef struct w_set_unique {
  w_entry_unique_t *entries;            /* Array of entries */
  unsigned int nb_entries;              /* Number of entries */
  unsigned int size;                    /* Size of array */
  union {
    unsigned int has_writes;            /* WRITE_BACK_ETL: Has the write set any real write (vs. visible reads) */
    unsigned int nb_acquired;           /* WRITE_BACK_CTL: Number of locks acquired */
  };
#ifdef USE_BLOOM_FILTER
  stm_word_t bloom;                     /* WRITE_BACK_CTL: Same Bloom filter as in TL2 */
#endif /* USE_BLOOM_FILTER */
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  khash_t(w_set_unique) *hash;          /* Hash table */
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
} ALIGNED w_set_unique_t;

typedef struct tx_conflict {
  stm_conflict_t entries;               /* Conflicting read/write set entries */
#ifdef CONFLICT_TRACKING
  struct stm_tx *other;                 /* Transaction that was conflicted with */
  stm_word_t status;                    /* Status of this transaction at time of conflict */
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
  const stm_lock_t *lock;               /* Pointer to contended lock */
#endif /* CONTENDED_LOCK_TRACKING */
} tx_conflict_t;

typedef struct cb_entry1 {              /* Callback entry */
  void (*f)(struct stm_tx *,
            const void *);              /* Function */
  const void *arg;                      /* Argument to be passed to function */
} cb_entry1_t;

typedef struct cb_entry2 {              /* Callback entry */
  void (*f)(const struct stm_tx *,
            const void *);              /* Function */
  const void *arg;                      /* Argument to be passed to function */
} cb_entry2_t;

typedef struct cb_entry3 {              /* Callback entry */
  void (*f)(const struct stm_tx *,
            const stm_tx_abort_t,
            const void *);              /* Function */
  const void *arg;                      /* Argument to be passed to function */
} cb_entry3_t;

#if !defined(MERGE_UNLOCK) && (CM == CM_MERGE || defined(MERGE_LOCK_CONFLICT)) && (DETECTION == TIME_BASED)
typedef enum {
  REVALIDATE_NONE = 0,
  REVALIDATE_CLOCK,
  REVALIDATE_RELOCK,
} revalidate_t;
#endif /* !MERGE_UNLOCK && (CM == CM_MERGE || MERGE_LOCK_CONFLICT) && (DETECTION == TIME_BASED) */

#if CM == CM_MERGE
typedef struct merge_context {
  union {
    stm_merge_policy_t policy;          /* Policy of the current merge */
    stm_merge_t result;                 /* Result of the current merge */
  };
  stm_merge_context_t context;          /* Public context of the current merge */
# if OPERATION_LOGGING != OPLOG_NONE
  unsigned int next;                    /* Manual: next position on the op log */
# endif /*OPERATION_LOGGING != OPLOG_NONE */
# if OPERATION_LOGGING == OPLOG_FULL
  struct {
    stm_op_t op_original;               /* Replay: original operation */
    stm_op_t op_current;                /* Replay: current operation */
    unsigned int op_log;                /* Replay: next position on the op log */
    unsigned int op_log_max;            /* Replay: max position on the op log */
    JMP_BUF env;                        /* Replay: context to handle conflicts during replay */
  } replay;
  struct {
    stm_union_t src;                    /* Update: new return value */
    unsigned char *dst;                 /* Update: position of the old return value on the op log */
    unsigned int size;                  /* Update: size of the return value */
  } update;
# endif /* OPERATION_LOGGING == OPLOG_FULL */
} merge_context_t;
#endif /* CM == CM_MERGE */

typedef struct stm_tx {                 /* Transaction descriptor */
  JMP_BUF env;                          /* Environment for setjmp/longjmp */
  stm_tx_attr_t attr;                   /* Transaction attributes (user-specified) */
  tx_status_t status;                   /* Transaction status */
  stm_version_t end;                    /* End timestamp (validity range) */
#if CM == CM_MERGE
  stm_version_t end_next;               /* Timestamp of current validation phase */
#endif /* CM == CM_MERGE */
#if !defined(MERGE_UNLOCK) && (CM == CM_MERGE || defined(MERGE_LOCK_CONFLICT)) && (DETECTION == TIME_BASED)
  revalidate_t revalidate;
#endif /* !MERGE_UNLOCK && (CM == CM_MERGE || MERGE_LOCK_CONFLICT) && (DETECTION == TIME_BASED) */
  r_set_t r_set;                        /* Read set */
  w_set_unique_t w_set_unique;          /* Unique write set */
  w_set_t w_set;                        /* Write set */
#if OPERATION_LOGGING != OPLOG_NONE
  stm_op_t op_current;                  /* Index to current operation (in bytes) */
  op_log_t op_log;                      /* Operation log */
#endif /* OPERATION_LOGGING != OPLOG_NONE */
#if CM == CM_MERGE
# if OPERATION_LOGGING == OPLOG_FULL
  unsigned int op_mergeable_delayed;    /* Operation is capable of delayed merging */
#  ifdef MERGE_JIT
  unsigned int op_mergeable_jit;        /* Operation is capable of JIT merging */
#  endif /* MERGE_JIT */
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  merge_context_t *merge;               /* Merge context */
# ifdef MERGE_FEEDBACK
  unsigned int feedback[64];
# endif /* MERGE_FEEDBACK */
#endif /* CM == CM_MERGE */
#ifdef IRREVOCABLE_ENABLED
  unsigned int irrevocable:4;           /* Is this execution irrevocable? */
#endif /* IRREVOCABLE_ENABLED */
  unsigned int nesting;                 /* Nesting level */
#if CM == CM_TIMESTAMP
  stm_word_t timestamp;                 /* Timestamp (not changed upon restart) */
#endif /* CM == CM_TIMESTAMP */
  const void *data[MAX_SPECIFIC];       /* Transaction-specific data (fixed-size array for better speed) */
  struct stm_tx *next;                  /* For keeping track of all transactional threads */
#ifdef CONFLICT_TRACKING
  pthread_t thread_id;                  /* Thread identifier (immutable) */
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
  const stm_lock_t *c_lock;             /* Pointer to contented lock (cause of abort) */
#endif /* CONTENDED_LOCK_TRACKING */
#if CM == CM_BACKOFF
  unsigned long backoff;                /* Maximum backoff duration */
  unsigned long seed;                   /* RNG seed */
#endif /* CM == CM_BACKOFF */
#if DESIGN == WRITE_BACK_ETL_VR
  int visible_reads;                    /* Should we use visible reads? */
#endif /* DESIGN == WRITE_BACK_ETL_VR */
#ifdef TM_STATISTICS
  unsigned int stat_extensions;         /* Total number of transaction extensions (cumulative) */
  unsigned int stat_commits;            /* Total number of commits (cumulative) */
  unsigned int stat_aborts;             /* Total number of aborts (cumulative) */
  unsigned int stat_relocks;            /* Total number of relocks (cumulative) */
  unsigned int stat_retries;            /* Total number of consecutive aborts (retries) */
  unsigned int stat_retries_max;        /* Maximum number of consecutive aborts (retries) */
# if CM == CM_MERGE
  unsigned int stat_merges_manual;      /* Number of manual merges started (not cumulative) */
#  if OPERATION_LOGGING == OPLOG_FULL
  unsigned int stat_merges_replay;      /* Number of replay merges started (not cumulative) */
#  endif /* OPERATION_LOGGING */
  unsigned int stat_merges_ok;          /* Number of merges successfully finished (not cumulative) */
  unsigned int stat_merges_retry;       /* Number of merges resulting in a retry (not cumulative) */
  unsigned int stat_reverted_reads;     /* Number of reverted reads (not cumulative) */
  unsigned int stat_reverted_writes;    /* Number of reverted writes (not cumulative) */
  unsigned int stat_reverted_ops;       /* Bytes of reverted operation log entries (not cumulative) */
# endif /* CM == CM_MERGE */
#endif /* TM_STATISTICS */
#ifdef TM_STATISTICS2
  unsigned long stat_reads;             /* Total number of transactional reads (cumulative) */
  unsigned long stat_writes;            /* Total number of transactional writes (cumulative) */
  unsigned int stat_aborts_1;           /* Total number of transactions that abort once or more (cumulative) */
  unsigned int stat_aborts_2;           /* Total number of transactions that abort twice or more (cumulative) */
  unsigned int stat_aborts_r[16];       /* Total number of transactions that abort wrt. abort reason (cumulative) */
# ifdef READ_LOCKED_DATA
  unsigned int stat_locked_reads_ok;    /* Successful reads of previous value */
  unsigned int stat_locked_reads_failed;/* Failed reads of previous value */
# endif /* READ_LOCKED_DATA */
  unsigned long long stat_work;         /* Cycle count at transaction startup */
  unsigned long long stat_work_merge;   /* Cycle count at first successful transaction merge */
#endif /* TM_STATISTICS2 */
} stm_tx_t;

#if OPERATION_LOGGING != OPLOG_NONE
typedef struct op_info {
#  if defined(DEBUG_OP_LOG) || defined(MERGE_FEEDBACK)
  char name[OP_NAME_SIZE];              /* String description of operation */
# endif /* DEBUG_OP_LOG || MERGE_FEEDBACK */
  ffi_cif fi;                           /* Function information struct */
# if OPERATION_LOGGING == OPLOG_FULL
  void (*f)();                          /* Pointer to function */
# endif /* OPERATION_LOGGING == OPLOG_FULL */
# if CM == CM_MERGE
#  ifdef MERGE_JIT
  stm_merge_policy_t policy[2];         /* Delayed and JIT merge policies */
#  else
  stm_merge_policy_t policy[1];         /* Delayed merge policy */
#  endif /* MERGE_JIT */
  stm_merge_cb_t delayed;               /* Delayed merge function */
#  ifdef MERGE_FEEDBACK
  unsigned int enabled;
  atomic_ulong executions;
  atomic_ulong repairs_attempted;
  atomic_ulong repairs_ok;
  atomic_ulong aborted_tx;
  atomic_ulong committed_tx;
#  endif /* MERGE_FEEDBACK */
# endif /* CM == CM_MERGE || CM == CM_MERGE */
} op_info_t;

typedef struct op_table {
  op_info_t *ids;                       /* Array of operations */
  unsigned int nb_ids;                  /* Number of operations */
  unsigned int size;                    /* Size of array */
} op_table_t;
#endif /* OPERATION_LOGGING != OPLOG_NONE */

/* This structure should be ordered by hot and cold variables */
typedef struct {
#if DETECTION == TIME_BASED
  stm_lock_t locks[LOCK_ARRAY_SIZE] ALIGNED;
#endif /* DETECTION == TIME_BASED */
  stm_version_t gclock ALIGNED;
#ifdef CONFLICT_TRACKING
  const stm_tx_policy_t (*conflict_cb)(const stm_tx_t *, const tx_conflict_t *);
#endif /* CONFLICT_TRACKING */
#if OPERATION_LOGGING != OPLOG_NONE
  op_table_t op_info;                   /* Table of known operations */
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  unsigned int nb_specific;             /* Number of specific slots used (<= MAX_SPECIFIC) */
  unsigned int nb_init_cb;
  cb_entry1_t init_cb[MAX_CB];          /* Init thread callbacks */
  unsigned int nb_exit_cb;
  cb_entry2_t exit_cb[MAX_CB];          /* Exit thread callbacks */
  unsigned int nb_start_cb;
  cb_entry2_t start_cb[MAX_CB];         /* Start callbacks */
  unsigned int nb_precommit_cb;
  cb_entry2_t precommit_cb[MAX_CB];     /* Commit callbacks */
  unsigned int nb_commit_cb;
  cb_entry2_t commit_cb[MAX_CB];        /* Commit callbacks */
  unsigned int nb_abort_cb;
  cb_entry3_t abort_cb[MAX_CB];         /* Abort callbacks */
  unsigned int initialized;             /* Has the library been initialized? */
#ifdef IRREVOCABLE_ENABLED
  stm_word_t irrevocable;               /* Irrevocability status */
#endif /* IRREVOCABLE_ENABLED */
  stm_word_t quiesce;                   /* Prevent threads from entering transactions upon quiescence */
  stm_word_t threads_nb;                /* Number of active threads */
  stm_tx_t *threads;                    /* Head of linked list of threads */
  pthread_mutex_t quiesce_mutex;        /* Mutex to support quiescence */
  pthread_cond_t quiesce_cond;          /* Condition variable to support quiescence */
#if DESIGN == WRITE_BACK_ETL_VR
  int vr_threshold;                     /* Number of retries before to switch to visible reads. */
#endif /* DESIGN == WRITE_BACK_ETL_VR */
} ALIGNED global_t;

extern global_t _tinystm;

/* ################################################################### *
 * FUNCTIONS DECLARATIONS
 * ################################################################### */

static stm_tx_policy_t
stm_conflict_handle_all(struct stm_tx *tx, const tx_conflict_t *conflict);
static stm_tx_policy_t
stm_conflict_handle(struct stm_tx *tx, const tx_conflict_t *conflict);

static NOINLINE void
stm_rollback(stm_tx_t *tx, stm_tx_abort_t reason);

#if CM == CM_TIMESTAMP
stm_tx_policy_t
cm_timestamp(struct stm_tx *tx, const tx_conflict_t *conflict);
#elif CM == CM_KARMA
stm_tx_policy_t
cm_karma(struct stm_tx *tx, const tx_conflict_t *conflict);
#elif CM == CM_MERGE
stm_tx_policy_t
cm_merge(struct stm_tx *tx, const tx_conflict_t *conflict);

stm_merge_t stm_merge(struct stm_tx *tx, const stm_conflict_t *c);
#endif /* CM */

#ifdef TRANSACTION_OPERATIONS
static NOINLINE int
stm_kill(struct stm_tx *tx, stm_tx_t *other, const stm_word_t status);
static NOINLINE void
stm_drop(struct stm_tx *tx);
#endif /* TRANSACTION_OPERATIONS */

#if OPERATION_LOGGING == OPLOG_FULL
static INLINE stm_op_t
int_stm_get_log(const stm_tx_t *tx);

static INLINE stm_write_t
int_stm_store_prev(const struct stm_tx *tx, const stm_write_t wt, const stm_op_t op);
static INLINE w_entry_t *
int_stm_store_latest(const struct stm_tx *tx, const stm_write_t wt, const stm_op_t op);
static INLINE stm_write_t *
int_stm_store_latest2(const struct stm_tx *tx, stm_write_t *wt, const stm_op_t op);
#endif /* OPERATION_LOGGING == OPLOG_FULL */

static void int_stm_undo_load(struct stm_tx *tx, r_entry_t *r, const int unlink
#if CM == CM_MERGE
  , const int dedup
#endif /* CM == CM_MERGE */
);

#ifdef READ_SET_ORDERED
# if CM == CM_MERGE
static INLINE void int_stm_load_position(struct stm_tx *, merge_context_t *, op_entry_t *);
# endif /* CM == CM_MERGE */
static INLINE stm_read_t *int_stm_get_load_position(struct stm_tx *);
#endif /* READ_SET_ORDERED */

/* ################################################################### *
 * INLINE FUNCTIONS
 * ################################################################### */

#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
static INLINE khint_t
kh_read_hash(const stm_read_t k) {
  const struct stm_tx *tx = stm_current_tx();
  assert(k.idx < tx->r_set.nb_entries);
  const r_entry_t *r = POINTER_FROM_READ(tx, k);

# ifdef READ_SET_SOURCE
#  ifdef __SSE4_2__
  const khint_t source = _mm_crc32_u64(0, (uintptr_t)r->source.idx);
#  else
  const khint_t source = (uintptr_t)r->source.idx;
#  endif /* __SSE4_2__ */
# else
  const khint_t source = 0;
# endif /* READ_SET_SOURCE */

# if OPERATION_LOGGING == OPLOG_FULL
#  ifdef __SSE4_2__
  const khint_t op = _mm_crc32_u64(source, (uintptr_t)r->op.idx);
#  else
  const khint_t op = source ^ (uintptr_t)r->op.idx;
#  endif /* __SSE4_2__ */
# else
  const khint_t op = source;
# endif /* OPERATION_LOGGING == OPLOG_FULL */

#  ifdef READ_SET_DETAILED
#   ifdef __SSE4_2__
  return _mm_crc32_u64(op, (uintptr_t)r->addr);
#   else
  return op ^ (uintptr_t)r->addr;
#   endif /* __SSE4_2__ */
#  elif DETECTION == TIME_BASED
#   ifdef __SSE4_2__
  return _mm_crc32_u64(op, (uintptr_t)r->lock);
#   else
  return op ^ (uintptr_t)r->lock;
#   endif /* __SSE4_2__ */
#  endif /* DETECTION */
}

static INLINE khint_t
kh_read_equal(const stm_read_t a, const stm_read_t b) {
  const struct stm_tx *tx = stm_current_tx();
  assert(a.idx < tx->r_set.nb_entries);
  const r_entry_t *r1 = POINTER_FROM_READ(tx, a);
  assert(b.idx < tx->r_set.nb_entries);
  const r_entry_t *r2 = POINTER_FROM_READ(tx, b);

# ifdef READ_SET_SOURCE
  const khint_t source = STM_SAME_WRITE(r1->source, r2->source);
# else
  const khint_t source = 1;
# endif /* READ_SET_SOURCE */

# if OPERATION_LOGGING == OPLOG_FULL
  const khint_t op = STM_SAME_OP(r1->op, r2->op);
# else
  const khint_t op = 1;
# endif /* OPERATION_LOGGING == OPLOG_FULL */

# ifdef READ_SET_DETAILED
  return source && op && r1->addr == r2->addr;
# elif DETECTION == TIME_BASED
  return source && op && r1->lock == r2->lock;
# endif /* DETECTION */
}
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */

#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
static INLINE khint_t
kh_write_hash(const stm_write_t k) {
  const struct stm_tx *tx = stm_current_tx();
  assert(k.idx < tx->w_set.nb_entries);
  const w_entry_t *w = POINTER_FROM_WRITE(tx, k);
# ifdef __SSE4_2__
#  if OPERATION_LOGGING == OPLOG_FULL
  return _mm_crc32_u64(_mm_crc32_u64(0, (uintptr_t)w->op.idx), (uintptr_t)POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->addr);
#  else
  return _mm_crc32_u64(0, (uintptr_t)POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->addr);
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
# else
#  if OPERATION_LOGGING == OPLOG_FULL
  return (uintptr_t)POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->addr ^ (uintptr_t)w->op.idx;
#  else
  return (uintptr_t)POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->addr;
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
# endif /* __SSE4_2__ */
}

static INLINE khint_t
kh_write_equal(const stm_write_t a, const stm_write_t b) {
  const struct stm_tx *tx = stm_current_tx();
  assert(a.idx < tx->w_set.nb_entries);
  const w_entry_t *w1 = POINTER_FROM_WRITE(tx, a);
  assert(b.idx < tx->w_set.nb_entries);
  const w_entry_t *w2 = POINTER_FROM_WRITE(tx, b);
# if OPERATION_LOGGING == OPLOG_FULL
  return POINTER_FROM_WRITE_UNIQUE(tx, w1->unique)->addr == POINTER_FROM_WRITE_UNIQUE(tx, w2->unique)->addr && STM_SAME_OP(w1->op, w2->op);
# else
  return POINTER_FROM_WRITE_UNIQUE(tx, w1->unique)->addr == POINTER_FROM_WRITE_UNIQUE(tx, w2->unique)->addr;
# endif /* OPERATION_LOGGING == OPLOG_FULL */
}
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */

#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
static INLINE khint_t
kh_write_unique_hash(const stm_write_unique_t k) {
  const struct stm_tx *tx = stm_current_tx();
  assert(k.idx < tx->w_set_unique.nb_entries);
  const w_entry_unique_t *wu = POINTER_FROM_WRITE_UNIQUE(tx, k);
  return (uintptr_t)wu->addr;
}

static INLINE khint_t
kh_write_unique_equal(const stm_write_unique_t a, const stm_write_unique_t b) {
  const struct stm_tx *tx = stm_current_tx();
  assert(a.idx < tx->w_set_unique.nb_entries);
  const w_entry_unique_t *wu1 = POINTER_FROM_WRITE_UNIQUE(tx, a);
  assert(b.idx < tx->w_set_unique.nb_entries);
  const w_entry_unique_t *wu2 = POINTER_FROM_WRITE_UNIQUE(tx, b);
  return wu1->addr == wu2->addr;
}
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */

#ifdef LOCK_IDX_SWAP
/*
 * Compute index in lock table (swap bytes to avoid consecutive addresses to have neighboring locks).
 */
static INLINE unsigned int
lock_idx_swap(unsigned int idx)
{
  return (idx & ~(unsigned int)0xFFFF) | ((idx & 0x00FF) << 8) | ((idx & 0xFF00) >> 8);
}
#endif /* LOCK_IDX_SWAP */

/*
 * Initialize quiescence support.
 */
static INLINE void
stm_quiesce_init(void)
{
  PRINT_DEBUG("==> stm_quiesce_init()\n");

  if (pthread_mutex_init(&_tinystm.quiesce_mutex, NULL) != 0) {
    fprintf(stderr, "Error creating mutex\n");
    exit(1);
  }
  if (pthread_cond_init(&_tinystm.quiesce_cond, NULL) != 0) {
    fprintf(stderr, "Error creating condition variable\n");
    exit(1);
  }
  _tinystm.quiesce = 0;
  _tinystm.threads_nb = 0;
  _tinystm.threads = NULL;
}

/*
 * Clean up quiescence support.
 */
static INLINE void
stm_quiesce_exit(void)
{
  PRINT_DEBUG("==> stm_quiesce_exit()\n");

  pthread_cond_destroy(&_tinystm.quiesce_cond);
  pthread_mutex_destroy(&_tinystm.quiesce_mutex);
}

/*
 * Called by each thread upon initialization for quiescence support.
 */
static INLINE void
stm_quiesce_enter_thread(stm_tx_t *tx)
{
  PRINT_DEBUG("==> stm_quiesce_enter_thread(%p)\n", tx);

  pthread_mutex_lock(&_tinystm.quiesce_mutex);
  /* Add new descriptor at head of list */
  tx->next = _tinystm.threads;
  _tinystm.threads = tx;
  _tinystm.threads_nb++;
  pthread_mutex_unlock(&_tinystm.quiesce_mutex);
}

/*
 * Called by each thread upon exit for quiescence support.
 */
static INLINE void
stm_quiesce_exit_thread(stm_tx_t *tx)
{
  stm_tx_t *t, *p;

  PRINT_DEBUG("==> stm_quiesce_exit_thread(%p)\n", tx);

  /* Can only be called if non-active */
  assert(!IS_ACTIVE(tx->status));

  pthread_mutex_lock(&_tinystm.quiesce_mutex);
  /* Remove descriptor from list */
  p = NULL;
  t = _tinystm.threads;
  while (t != tx) {
    assert(t != NULL);
    p = t;
    t = t->next;
  }
  if (p == NULL)
    _tinystm.threads = t->next;
  else
    p->next = t->next;
  _tinystm.threads_nb--;
  if (_tinystm.quiesce) {
    /* Wake up someone in case other threads are waiting for us */
    pthread_cond_signal(&_tinystm.quiesce_cond);
  }
  pthread_mutex_unlock(&_tinystm.quiesce_mutex);
}

/*
 * Wait for all transactions to be block on a barrier.
 */
static NOINLINE void
stm_quiesce_barrier(stm_tx_t *tx, void (* const f)(const void *), const void *arg)
{
  PRINT_DEBUG("==> stm_quiesce_barrier()\n");

  /* Can only be called if non-active */
  assert(tx == NULL || !IS_ACTIVE(tx->status));

  pthread_mutex_lock(&_tinystm.quiesce_mutex);
  /* Wait for all other transactions to block on barrier */
  _tinystm.threads_nb--;
  if (_tinystm.quiesce == 0) {
    /* We are first on the barrier */
    _tinystm.quiesce = 1;
  }
  while (_tinystm.quiesce) {
    if (_tinystm.threads_nb == 0) {
      /* Everybody is blocked */
      if (f != NULL)
        f(arg);
      /* Release transactional threads */
      _tinystm.quiesce = 0;
      pthread_cond_broadcast(&_tinystm.quiesce_cond);
    } else {
      /* Wait for other transactions to stop */
      pthread_cond_wait(&_tinystm.quiesce_cond, &_tinystm.quiesce_mutex);
    }
  }
  _tinystm.threads_nb++;
  pthread_mutex_unlock(&_tinystm.quiesce_mutex);
}

/*
 * Wait for all transactions to be out of their current transaction.
 */
static INLINE int
stm_quiesce(const stm_tx_t *tx, const int block)
{
  const stm_tx_t *t;
#ifdef TRANSACTION_OPERATIONS
  stm_word_t s, c;
#endif /* TRANSACTION_OPERATIONS */

  PRINT_DEBUG("==> stm_quiesce(%p,%d)\n", tx, block);

  if (IS_ACTIVE(tx->status)) {
    /* Only one active transaction can quiesce at a time, others must abort */
    if (pthread_mutex_trylock(&_tinystm.quiesce_mutex) != 0)
      return 1;
  } else {
    /* We can safely block because we are inactive */
    pthread_mutex_lock(&_tinystm.quiesce_mutex);
  }
  /* We own the lock at this point */
  if (block)
    ATOMIC_STORE_REL(&_tinystm.quiesce, 2);
  /* Make sure we read latest status data */
  ATOMIC_MB_FULL;
  /* Not optimal as we check transaction sequentially and might miss some inactivity states */
  for (t = _tinystm.threads; t != NULL; t = t->next) {
    if (t == tx)
      continue;
    /* Wait for all other transactions to become inactive */
#ifdef TRANSACTION_OPERATIONS
    s = t->status;
    if (IS_ACTIVE(s)) {
      c = GET_STATUS_COUNTER(s);
      do {
        s = t->status;
      } while (IS_ACTIVE(s) && c == GET_STATUS_COUNTER(s));
    }
#else /* TRANSACTION_OPERATIONS */
    while (IS_ACTIVE(t->status))
      ;
#endif /* TRANSACTION_OPERATIONS */
  }
  if (!block)
    pthread_mutex_unlock(&_tinystm.quiesce_mutex);
  return 0;
}

/*
 * Check if transaction must block.
 */
static INLINE int
stm_check_quiesce(stm_tx_t *tx)
{
  stm_word_t s;

  /* Must be called upon start (while already active but before acquiring any lock) */
  assert(IS_ACTIVE(tx->status));

  /* ATOMIC_MB_FULL;  The full memory barrier is not required here since quiesce
   * is atomic. Only a compiler barrier is needed to avoid reordering. */
  ATOMIC_CB;

  if (unlikely(ATOMIC_LOAD_ACQ(&_tinystm.quiesce) == 2)) {
#ifdef IRREVOCABLE_ENABLED
    /* Only test it when quiesce == 2, it avoids one comparison for fast-path. */
    /* TODO check if it is correct. */
    if (unlikely((tx->irrevocable & 0x08) != 0)) {
      /* Serial irrevocable mode: we are executing alone */
      return 0;
    }
#endif /* IRREVOCABLE_ENABLED */
    s = ATOMIC_LOAD(&tx->status);
    SET_STATUS(tx->status, TX_IDLE);
    while (ATOMIC_LOAD_ACQ(&_tinystm.quiesce) == 2) {
#ifdef WAIT_YIELD
      sched_yield();
#endif /* WAIT_YIELD */
    }
    SET_STATUS(tx->status, GET_STATUS(s));
    return 1;
  }
  return 0;
}

/*
 * Release threads blocked after quiescence.
 */
static INLINE void
stm_quiesce_release(stm_tx_t *tx)
{
  ATOMIC_STORE_REL(&_tinystm.quiesce, 0);
  pthread_mutex_unlock(&_tinystm.quiesce_mutex);
}

/*
 * Reset clock and timestamps
 */
static INLINE void
rollover_clock(const void *arg)
{
  PRINT_DEBUG("==> rollover_clock()\n");

  /* Reset clock */
  CLOCK = 0;
  /* Reset timestamps */
#if DETECTION == TIME_BASED
  memset((void *)_tinystm.locks, 0, LOCK_ARRAY_SIZE * sizeof(*_tinystm.locks));
#endif /* DETECTION == TIME_BASED */
#if MEMORY_MANAGEMENT != MM_NONE
  /* Reset GC */
  gc_reset();
#endif /* MEMORY_MANAGEMENT != MM_NONE */
}

static INLINE r_entry_t *
int_stm_did_load(struct stm_tx *tx, const void *s
#if OPERATION_LOGGING == OPLOG_FULL
  , const stm_op_t op
#endif /* OPERATION_LOGGING == OPLOG_FULL */
#ifdef READ_SET_SOURCE
  , const stm_write_t wt
#endif /* READ_SET_SOURCE */
) {
#if DESIGN == WRITE_BACK_ETL_VR
  /* TODO case of visible read is not handled */
#endif /* DESIGN == WRITE_BACK_ETL_VR */

#if READ_SET == RW_ARRAY || READ_SET == RW_ADAPTIVE
  if (
# if READ_SET == RW_ADAPTIVE
    !kh_size(tx->r_set.hash)
# else
    1
# endif /* READ_SET == RW_ADAPTIVE */
  ) {
#ifdef READ_SET_ORDERED
    const unsigned int ordered = tx->attr.read_set_ordered;
#endif /* READ_SET_ORDERED */

    r_entry_t *r;
    stm_read_t rt = { .idx =
# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
      READ_RESERVED_IDX + 1
# else
      0
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
    };
# ifdef READ_SET_ORDERED
    if (ordered) {
      rt = tx->r_set.head;

#  if OPERATION_LOGGING == OPLOG_FULL
      if (OP_VALID(tx, op)) {
        const op_entry_t *e = GET_LOG_ENTRY(tx, op.idx);
        if (likely(READ_VALID_FAST(tx, e->reads)))
          rt = e->reads;
      }
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
    }
# endif /* READ_SET_ORDERED */
    for (; likely(READ_VALID_FAST(tx, rt));
      rt =
# ifdef READ_SET_ORDERED
      ordered ? r->next :
# endif /* READ_SET_ORDERED */
      READ_FROM_POINTER(tx, r + 1)
    ) {
      r = POINTER_FROM_READ(tx, rt);
# if CM == CM_MERGE && defined(READ_SET_ORDERED)
      if (tx->attr.read_set_ordered)
        assert(r->lock);
      else if (!r->lock)
        continue;
# elif DETECTION == TIME_BASED
      if (!r->lock)
        continue;
# endif /* CM == CM_MERGE && READ_SET_ORDERED */
      /* Return first match */
      if (
# ifdef READ_SET_DETAILED
        /* Fine-grained address-based matching */
        r->addr == (stm_word_t *)s
# elif DETECTION == TIME_BASED
        /* Coarse-grained lock-based matching */
        r->lock == (stm_lock_t *)s
# endif /* DETECTION */
# if OPERATION_LOGGING == OPLOG_FULL
        /* Fine-grained per-operation address-based matching */
        && STM_SAME_OP(r->op, op)
# endif /* OPERATION_LOGGING == OPLOG_FULL */
# ifdef READ_SET_SOURCE
        && STM_SAME_WRITE(r->source, wt)
# endif /* READ_SET_SOURCE */
      )
        return r;
    }

    return NULL;
  }
#endif /* READ_SET == RW_ARRAY || READ_SET == RW_ADAPTIVE */
#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
# ifdef READ_SET_DETAILED
  /* Fine-grained per-operation address-based matching */
  tx->r_set.entries[READ_RESERVED_IDX].addr = s;
# elif DETECTION == TIME_BASED
  /* Coarse-grained lock-based matching */
  tx->r_set.entries[READ_RESERVED_IDX].lock = (stm_lock_t *)s;
# endif /* DETECTION */
# if OPERATION_LOGGING == OPLOG_FULL
  tx->r_set.entries[READ_RESERVED_IDX].op = op;
# endif /* OPERATION_LOGGING == OPLOG_FULL */
# ifdef READ_SET_SOURCE
  tx->r_set.entries[READ_RESERVED_IDX].source = wt;
# endif /* READ_SET_SOURCE */
  const khiter_t it = kh_get(r_set, tx->r_set.hash, READ_FROM_POINTER(tx, &tx->r_set.entries[READ_RESERVED_IDX]));
  assert(it == kh_end(tx->r_set.hash) || READ_VALID(tx, kh_key(tx->r_set.hash, it)));
  return it != kh_end(tx->r_set.hash) ? POINTER_FROM_READ(tx, kh_key(tx->r_set.hash, it)) : NULL;
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
}

#ifdef READ_SET_DETAILED
static INLINE r_entry_t *
int_stm_did_load2(struct stm_tx *tx, const stm_word_t *addr, const stm_op_t op) {
# ifdef READ_SET_ORDERED
  const unsigned int ordered = tx->attr.read_set_ordered;
# endif /* READ_SET_ORDERED */
  r_entry_t *r;
  stm_read_t rt = { .idx =
# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
    READ_RESERVED_IDX + 1
# else
    0
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
  };

# ifdef READ_SET_ORDERED
  if (ordered) {
    rt = tx->r_set.head;

#  if OPERATION_LOGGING == OPLOG_FULL
    if (OP_VALID(tx, op)) {
      const op_entry_t *e = GET_LOG_ENTRY(tx, op.idx);
      if (likely(READ_VALID_FAST(tx, e->reads)))
        rt = e->reads;
    }
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
  }
# endif /* READ_SET_ORDERED */
  for (; likely(READ_VALID_FAST(tx, rt));
    rt = (
# ifdef READ_SET_ORDERED
    ordered ? r->next :
# endif /* READ_SET_ORDERED */
    READ_FROM_POINTER(tx, r + 1))
  ) {
    r = POINTER_FROM_READ(tx, rt);
# if CM == CM_MERGE && defined(READ_SET_ORDERED)
    if (tx->attr.read_set_ordered)
      assert(r->lock);
    else if (!r->lock)
      continue;
# elif DETECTION == TIME_BASED
    if (!r->lock)
      continue;
# endif /* CM == CM_MERGE && READ_SET_ORDERED */

    /* Return first match */
    if (r->addr == addr
# if OPERATION_LOGGING == OPLOG_FULL
        && STM_SAME_OP(r->op, op)
# endif /* OPERATION_LOGGING == OPLOG_FULL */
      )
      return r;
  }

  return NULL;
}
#endif /* READ_SET_DETAILED */

/*
 * Check if stripe has been read previously.
 */
static INLINE r_entry_t *
stm_has_read(struct stm_tx *tx, const stm_word_t *addr
#ifdef READ_SET_SOURCE
  , const stm_write_t wt
#endif /* READ_SET_SOURCE */
  ) {
  PRINT_DEBUG("==> stm_has_read(%p[%lu],%p)\n", tx, (unsigned long)tx->end, addr);
  assert(addr == ALIGN_ADDR(addr));
  r_entry_t *r;

#ifdef READ_SET_DETAILED
  r = int_stm_did_load(tx, addr
# if OPERATION_LOGGING == OPLOG_FULL
    , int_stm_get_log(tx)
# endif /* OPERATION_LOGGING == OPLOG_FULL */
#ifdef READ_SET_SOURCE
    , wt
#endif /* READ_SET_SOURCE */
  );
  assert(!r || (r && addr == r->addr));
#elif DETECTION == TIME_BASED
  r = int_stm_did_load(tx, GET_LOCK(addr)
# if OPERATION_LOGGING == OPLOG_FULL
    , int_stm_get_log(tx)
# endif /* OPERATION_LOGGING == OPLOG_FULL */
#ifdef READ_SET_SOURCE
    , wt
#endif /* READ_SET_SOURCE */
  );
  assert(!r || (r && GET_LOCK(addr) == r->lock));
#endif /* DETECTION */
#if OPERATION_LOGGING == OPLOG_FULL
  assert(!r || (r && STM_SAME_OP(int_stm_get_log(tx), r->op)));
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  return r;
}

static INLINE w_entry_unique_t *
int_stm_did_store_unique(const stm_tx_t *tx, stm_word_t *addr) {
  assert(addr == ALIGN_ADDR(addr));

#ifdef USE_BLOOM_FILTER
  const stm_word_t mask = FILTER_BITS(addr);
  if ((tx->w_set_unique.bloom & mask) != mask)
    return NULL;
#endif /* USE_BLOOM_FILTER */

#if WRITE_SET_UNIQUE == RW_ARRAY || WRITE_SET_UNIQUE == RW_ADAPTIVE
  if (
# if WRITE_SET_UNIQUE == RW_ADAPTIVE
    !kh_size(tx->w_set_unique.hash)
# else
    1
# endif /* WRITE_SET_UNIQUE == RW_ADAPTIVE */
  ) {
    for (w_entry_unique_t *wu = tx->w_set_unique.entries + tx->w_set_unique.nb_entries - 1; likely(WRITE_UNIQUE_POINTER_VALID(tx, wu)); --wu) {
# if DETECTION == TIME_BASED
      assert(wu->lock);
# endif /* DETECTION == TIME_BASED */
      if (wu->addr == addr)
        return wu;
    }
    return NULL;
  }
#endif /* WRITE_SET_UNIQUE == RW_ARRAY || WRITE_SET_UNIQUE == RW_ADAPTIVE */
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  tx->w_set_unique.entries[WRITE_RESERVED_IDX].addr = addr;
  const khiter_t it = kh_get(w_set_unique, tx->w_set_unique.hash, WRITE_UNIQUE_FROM_POINTER(tx, &tx->w_set_unique.entries[WRITE_RESERVED_IDX]));
  assert(it == kh_end(tx->w_set_unique.hash) || WRITE_UNIQUE_VALID(tx, kh_key(tx->w_set_unique.hash, it)));
  return it != kh_end(tx->w_set_unique.hash) ? POINTER_FROM_WRITE_UNIQUE(tx, kh_key(tx->w_set_unique.hash, it)) : NULL;
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */

  return NULL;
}

static INLINE w_entry_t *
int_stm_did_store(struct stm_tx *tx, const w_entry_unique_t *wu
#if OPERATION_LOGGING == OPLOG_FULL
  , const stm_op_t op
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  ) {
  assert(WRITE_UNIQUE_POINTER_VALID(tx, wu));

  if (!WRITE_VALID_FAST(tx, wu->latest))
    return NULL;

    /* Look for write */
#if OPERATION_LOGGING == OPLOG_FULL
# if WRITE_SET == RW_ARRAY || WRITE_SET == RW_ADAPTIVE
  if (
#  if WRITE_SET == RW_ADAPTIVE
    !kh_size(tx->w_set.hash)
#  else
    1
#  endif /* WRITE_SET == RW_ADAPTIVE */
  ) {
    const stm_write_t prev = int_stm_store_prev(tx, wu->latest, op);
    return WRITE_VALID_FAST(tx, prev) ? POINTER_FROM_WRITE(tx, prev) : NULL;
  }
# endif /* WRITE_SET == RW_ARRAY || WRITE_SET == RW_ADAPTIVE */
# if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
  assert(tx->w_set.entries[WRITE_RESERVED_IDX].unique.idx == WRITE_RESERVED_IDX);
  tx->w_set_unique.entries[WRITE_RESERVED_IDX].addr = wu->addr;
  tx->w_set.entries[WRITE_RESERVED_IDX].op = op;
  const khiter_t it = kh_get(w_set, tx->w_set.hash, WRITE_FROM_POINTER(tx, &tx->w_set.entries[WRITE_RESERVED_IDX]));
  assert(it == kh_end(tx->w_set.hash) || WRITE_VALID(tx, kh_key(tx->w_set.hash, it)));
  return it != kh_end(tx->w_set.hash) ? POINTER_FROM_WRITE(tx, kh_key(tx->w_set.hash, it)) : NULL;
# endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */
#else
  return WRITE_VALID_FAST(tx, wu->latest) ? POINTER_FROM_WRITE(tx, wu->latest) : NULL;
#endif /* OPERATION_LOGGING == OPLOG_FULL */
}

/*
 * Check if address has been written previously. Used for reads; during merge
 * will return the latest write that occurred before the current operation.
 */
static INLINE w_entry_t *
stm_has_written(stm_tx_t *tx, stm_word_t *addr) {
  PRINT_DEBUG("==> stm_has_written(%p[%lu],%p)\n", tx, (unsigned long)tx->end, addr);

  const w_entry_unique_t *wu = int_stm_did_store_unique(tx, addr);
  if (!wu || !WRITE_VALID_FAST(tx, wu->latest))
    return NULL;

  /* Look for write */
  if (
#if CM == CM_MERGE
      likely(!tx->merge)
#else
      1
#endif /* CM == CM_MERGE */
    ) {
    /* Regular operation, no merging */
    return WRITE_VALID_FAST(tx, wu->latest) ? POINTER_FROM_WRITE(tx, wu->latest) : NULL;
#if CM == CM_MERGE
  } else {
# if OPERATION_LOGGING == OPLOG_FULL
    if (tx->merge->policy == STM_MERGE_POLICY_REPLAY) {
      /* Replay merge, return the latest write before the end of the replay */
      return int_stm_store_latest(tx, wu->latest, ((stm_op_t){ .idx = tx->merge->replay.op_log_max }));
    } else {
      /* Manual merge, return the latest write before the current operation */
      return int_stm_store_latest(tx, wu->latest, tx->merge->context.current);
    }
# else
    return int_stm_did_store(tx, wu);
# endif /* OPERATION_LOGGING == OPLOG_FULL */
#endif /* CM == CM_MERGE */
  }
}

/*
 * Check if address has been written previously. Used for writes; during merge
 * will return the latest write that occurred within the current operation.
 */
static INLINE w_entry_t *
stm_has_written_current(stm_tx_t *tx, const w_entry_unique_t *wu
#if OPERATION_LOGGING == OPLOG_FULL
  , const stm_op_t op
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  ) {
  PRINT_DEBUG("==> stm_has_written_op(%p[%lu],%p,%ld)\n", tx, (unsigned long)tx->end, wu, op.idx);

  /* Look for write */
#if CM == CM_MERGE
  if (unlikely(tx->merge)) {
    /* Must return the latest write within the current operation */
    return int_stm_did_store(tx, wu
# if OPERATION_LOGGING == OPLOG_FULL
      , op
# endif /* OPERATION_LOGGING == OPLOG_FULL */
    );
  }
#endif /* CM == CM_MERGE */

  w_entry_t *w = WRITE_VALID_FAST(tx, wu->latest) ? POINTER_FROM_WRITE(tx, wu->latest) : NULL;
#if OPERATION_LOGGING == OPLOG_FULL
  /* Check the latest write is from the desired operation */
  return w && STM_SAME_OP(w->op, op) ? w : NULL;
#else
  return w;
#endif /* OPERATION_LOGGING == OPLOG_FULL */
}

/*
 * (Re)allocate read set entries.
 */
static NOINLINE void
stm_allocate_rs_entries(stm_tx_t *tx, const int extend)
{
  PRINT_DEBUG("==> stm_allocate_rs_entries(%p[%lu],%d)\n", tx, (unsigned long)tx->end, extend);

  if (extend) {
    /* Extend read set */
    unsigned int new_size = 2 * tx->r_set.size;
    tx->r_set.entries = (r_entry_t *)xrealloc(tx->r_set.entries, new_size * sizeof(r_entry_t));
    memset(tx->r_set.entries + tx->r_set.size, 0, tx->r_set.size * sizeof(r_entry_t));
    tx->r_set.size = new_size;
  } else {
    /* Allocate read set */
    tx->r_set.entries = (r_entry_t *)xmalloc_aligned(tx->r_set.size * sizeof(r_entry_t));
    memset(tx->r_set.entries, 0, tx->r_set.size * sizeof(r_entry_t));
  }
}

/*
 * (Re)allocate write set entries.
 */
static NOINLINE void
stm_allocate_ws_entries(stm_tx_t *tx, const int extend)
{
  PRINT_DEBUG("==> stm_allocate_ws_entries(%p[%lu],%d)\n", tx, (unsigned long)tx->end, extend);

  if (extend) {
    /* Extend read set */
    unsigned int new_size = 2 * tx->w_set.size;
    tx->w_set.entries = (w_entry_t *)xrealloc(tx->w_set.entries, new_size * sizeof(w_entry_t));
    memset(tx->w_set.entries + tx->w_set.size, 0, tx->w_set.size * sizeof(w_entry_t));
    tx->w_set.size = new_size;
  } else {
#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
    assert(!stm_active_tx(tx));
    kh_clear(w_set, tx->w_set.hash);
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */

    /* Allocate read set */
    tx->w_set.entries = (w_entry_t *)xmalloc_aligned(tx->w_set.size * sizeof(w_entry_t));
    memset(tx->w_set.entries, 0, tx->w_set.size * sizeof(w_entry_t));
  }
}

static NOINLINE void
stm_allocate_ws_unique_entries(stm_tx_t *tx, const int extend)
{
  PRINT_DEBUG("==> stm_allocate_ws_unique_entries(%p[%lu],%d)\n", tx, (unsigned long)tx->end, extend);

#if defined(CONFLICT_TRACKING)
  int i, first = (extend ? tx->w_set_unique.size : 0);
#endif /* defined(CONFLICT_TRACKING) */
#if MEMORY_MANAGEMENT != MM_NONE
  void *a;
#endif /* MEMORY_MANAGEMENT */

  if (extend) {
    /* Extend write set */
    /* Transaction must be inactive for WRITE_THROUGH or WRITE_BACK_ETL */
    tx->w_set_unique.size *= 2;
#if MEMORY_MANAGEMENT != MM_NONE
    a = tx->w_set_unique.entries;
    tx->w_set_unique.entries = (w_entry_unique_t *)xmalloc_aligned(tx->w_set_unique.size * sizeof(w_entry_unique_t));
    memcpy(tx->w_set_unique.entries, a, tx->w_set_unique.size / 2 * sizeof(w_entry_unique_t));
    gc_free(a, GET_CLOCK);
#else /* MEMORY_MANAGEMENT = MM_NONE */
    tx->w_set_unique.entries = (w_entry_unique_t *)xrealloc(tx->w_set_unique.entries, tx->w_set_unique.size * sizeof(w_entry_unique_t));
#endif /* MEMORY_MANAGEMENT */
  } else {
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
    assert(!stm_active_tx(tx));
    kh_clear(w_set_unique, tx->w_set_unique.hash);
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */

    /* Allocate write set */
    tx->w_set_unique.entries = (w_entry_unique_t *)xmalloc_aligned(tx->w_set_unique.size * sizeof(w_entry_unique_t));
  }
  /* Ensure that memory is aligned. */
#if DETECTION == TIME_BASED
  assert((((stm_word_t)tx->w_set_unique.entries) & OWNED_MASK) == 0);
#endif /* DETECTION == TIME_BASED */

#ifdef CONFLICT_TRACKING
  /* Initialize fields */
  for (i = first; i < tx->w_set_unique.size; i++)
    tx->w_set_unique.entries[i].tx = tx;
#endif /* CONFLICT_TRACKING */
}

#if OPERATION_LOGGING != OPLOG_NONE
/* (Re)allocate operation log entries. */
static NOINLINE void
stm_allocate_ol_entries(stm_tx_t *tx, const int extend)
{
  PRINT_DEBUG("==> stm_allocate_ol_entries(%p[%lu],%d)\n", tx, (unsigned long)tx->end, extend);

  if (extend) {
    /* Extend operation log */
    tx->op_log.size *= 2;
    tx->op_log.entries = xrealloc(tx->op_log.entries, tx->op_log.size * sizeof(*tx->op_log.entries));
  } else {
    /* Allocate operation log */
    tx->op_log.entries = xmalloc_aligned(tx->op_log.size * sizeof(*tx->op_log.entries));
  }
}

/* Returns the current log operation. Used for tagging read/write entries. Distinguishes between the current merge operation and the current transaction operation. */
static INLINE stm_op_t
int_stm_get_log(const stm_tx_t *tx)
{
# if CM == CM_MERGE
  if (tx->merge)
    return tx->merge->context.current;
# endif /* CM == CM_MERGE */
  return tx->op_current;
}
#endif /* OPERATION_LOGGING != OPLOG_NONE */

static INLINE r_entry_t *
stm_add_to_rs(stm_tx_t *tx, const stm_word_t *addr
#if DETECTION == TIME_BASED
  , const stm_lock_t *lock, const stm_version_t version
#endif /* DETECTION == TIME_BASED */
#ifdef READ_SET_DETAILED
  , const stm_word_t value
#endif /* READ_SET_DETAILED */
#ifdef READ_SET_TAGGED
  , const uintptr_t tag
#endif /* READ_SET_TAGGED */
#ifdef READ_SET_SOURCE
  , const stm_write_t source
#endif /* READ_SET_SOURCE */
) {
  r_entry_t *r = NULL;
#if OPERATION_LOGGING == OPLOG_FULL || defined(READ_SET_ORDERED) || READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
  stm_read_t rt;
#endif /* OPERATION_LOGGING == OPLOG_FULL || READ_SET_ORDERED || READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */

  /* No need to add to read set for read-only transaction */
  if (tx->attr.read_only)
    return NULL;

  /* Retrieve a free read set entry */
#ifdef READ_SET_ORDERED
  /* Check the free list */
  if (tx->attr.read_set_ordered && READ_VALID_FAST(tx, tx->r_set.free)) {
    r = POINTER_FROM_READ(tx, tx->r_set.free);
    tx->r_set.free = r->next;
  }
#endif /* READ_SET_ORDERED */
  if (!r) {
    /* Grab an entry from the end of the array, or reallocate if it is full */
    if (unlikely(tx->r_set.nb_entries == tx->r_set.size))
      stm_allocate_rs_entries(tx, 1);
#if READ_SET == RW_ADAPTIVE
    else if (!kh_size(tx->r_set.hash) && tx->r_set.nb_entries == RW_ADAPTIVE_THRESHOLD) {
      /* Reached the threshold; add all entries to the hash table */
      for (rt.idx = READ_RESERVED_IDX + 1; READ_VALID_FAST(tx, rt); ++rt.idx) {
        int ret;
        assert(rt.idx != READ_RESERVED_IDX);
        r = POINTER_FROM_READ(tx, rt);
        if (
#if CM == CM_MERGE
# ifdef READ_SET_ORDERED
          !tx->attr.read_set_ordered && r->lock
# else
          r->lock
# endif /* READ_SET_ORDERED */
#else
          1
#endif /* CM == CM_MERGE */
        ) {
          kh_put(r_set, tx->r_set.hash, rt, &ret);
          if (!ret)
            int_stm_undo_load(tx, r, 1
# if CM == CM_MERGE
              , 0
# endif /* CM == CM_MERGE */
            );
        }
      }
    }
#endif /* READ_SET == RW_ADAPTIVE */
    r = &tx->r_set.entries[tx->r_set.nb_entries++];
  }

  assert(READ_POINTER_VALID(tx, r));
  /* Add address and version to read set */
#ifdef READ_SET_SOURCE
  r->source = source;
#endif /* READ_SET_SOURCE */
#if DETECTION == TIME_BASED
  r->lock = lock;
  r->version = version;
#endif /* DETECTION == TIME_BASED */
#ifdef READ_SET_DETAILED
  r->addr = addr;
  r->value = value;
#endif /* READ_SET_DETAILED */
#if OPERATION_LOGGING != OPLOG_NONE
  r->op = int_stm_get_log(tx);
#endif /* OPERATION_LOGGING != OPLOG_NONE */
#ifdef READ_SET_TAGGED
  r->tag = tag;
#endif /* READ_SET_TAGGED */

#if OPERATION_LOGGING == OPLOG_FULL || defined(READ_SET_ORDERED) || READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
  rt = READ_FROM_POINTER(tx, r);
#endif /* OPERATION_LOGGING == OPLOG_FULL || READ_SET_ORDERED || READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */

#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
  if (
# if READ_SET == RW_ADAPTIVE
    kh_size(tx->r_set.hash)
# else
    1
# endif /* READ_SET == RW_ADAPTIVE */
  ) {
    int ret;
# if !defined(NO_DUPLICATES_IN_RW_SETS)
    khiter_t it = kh_put(r_set, tx->r_set.hash, rt, &ret);
    /* Early deduplication */
    if (!ret) {
      if (
#  ifdef READ_SET_ORDERED
        !tx->attr.read_set_ordered
#  else
        1
#  endif /* READ_SET_ORDERED */
      ) {
        assert(r == &tx->r_set.entries[tx->r_set.nb_entries - 1]);
        --tx->r_set.nb_entries;
#  ifdef READ_SET_ORDERED
      } else {
        /* Put it on the free list */
        r->next = tx->r_set.free;
        tx->r_set.free = rt;
#  endif /* READ_SET_ORDERED */
      }

      return POINTER_FROM_READ(tx, kh_key(tx->r_set.hash, it));
    }
# else
    kh_put(r_set, tx->r_set.hash, rt, &ret);
# endif /* ! NO_DUPLICATES_IN_RW_SETS */
    assert(ret > 0);
  }
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */

#ifdef READ_SET_ORDERED
  /* Insert this entry in the ordered read set */
  if (tx->attr.read_set_ordered) {
# if CM == CM_MERGE
    stm_read_t *tail;
    /* Force eager computation */
    if (tx->merge)
      tail = int_stm_get_load_position(tx);
    else
      tail = &tx->r_set.tail;
# else
    stm_read_t *tail = &tx->r_set.tail;
# endif /* CM */
    assert(!STM_SAME_READ(rt, *tail));
    r_entry_t *t = READ_VALID_FAST(tx, *tail) ? POINTER_FROM_READ(tx, *tail) : NULL;
    assert(!t || !STM_SAME_READ(rt, t->next));
    r->next = t ? t->next : STM_INVALID_READ;
# if CM == CM_MERGE
    /* Must also update tail of the read set */
    if (tx->merge && STM_SAME_READ(*tail, tx->r_set.tail))
      tx->r_set.tail = rt;
# endif /* CM == CM_MERGE */
    *tail = t ? (t->next = rt) : (tx->r_set.head = rt);
  } else {
# if CM == CM_MERGE
    if (tx->merge) {
      stm_read_t *last = int_stm_get_load_position(tx);
      assert((last && READ_VALID_FAST(tx, *last)) || (tx->merge->policy == STM_MERGE_POLICY_REPLAY && STM_SAME_READ(tx->merge->context.read, STM_INVALID_READ)));
      if (!STM_SAME_READ(rt, *last)) {
        stm_read_t next = { .idx = READ_VALID_FAST(tx, *last) ? last->idx + 1 :
#  if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
          READ_RESERVED_IDX + 1
#  else
          0
#  endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
        };
        assert(READ_VALID_FAST(tx, next));
        r_entry_t *rnext = POINTER_FROM_READ(tx, next);
        /* If the next entry is free, move the current entry there */
        if (!rnext->lock) {
#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
          if (
# if READ_SET == RW_ADAPTIVE
            kh_size(tx->r_set.hash)
# else
            1
# endif /* READ_SET == RW_ADAPTIVE */
          ) {
            khiter_t it = kh_get(r_set, tx->r_set.hash, rt);
            assert(it != kh_end(tx->r_set.hash) && STM_SAME_READ(rt, kh_key(tx->r_set.hash, it)));
            kh_del(r_set, tx->r_set.hash, it);
          }
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */

          memcpy(rnext, r, sizeof(*r));
          --tx->r_set.nb_entries;

          r = rnext;
          rt = next;

#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
          if (
# if READ_SET == RW_ADAPTIVE
            kh_size(tx->r_set.hash)
# else
            1
# endif /* READ_SET == RW_ADAPTIVE */
          ) {
            int ret;
            kh_put(r_set, tx->r_set.hash, rt, &ret);
            assert(ret > 0);
          }
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
        } else {
          /* Insertion of a new read set entry during merge requires READ_SET_ORDERED */
          tx->attr.read_set_ordered = 1;
          stm_rollback(tx, STM_ABORT_OTHER);
        }
      }
    }
# endif /* CM == CM_MERGE */
    r->next = STM_INVALID_READ;
  }
#else
# if CM == CM_MERGE
  assert(!tx->merge ||
#  if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
    tx->r_set.nb_entries == READ_RESERVED_IDX + 1
#  else
    tx->r_set.nb_entries == 0
#  endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
  );
# endif /* CM == CM_MERGE */
#endif /* READ_SET_ORDERED */

#if OPERATION_LOGGING == OPLOG_FULL
  /* Record this read in the operation log entry */
  if (OP_VALID(tx, r->op)) {
    op_entry_t *e = GET_LOG_ENTRY(tx, r->op.idx);
    if (!READ_VALID_FAST(tx, e->reads)
# ifdef READ_SET_ORDERED
      || (tx->attr.read_set_ordered && STM_SAME_READ(r->next, e->reads))
# endif /* READ_SET_ORDERED */
    )
      e->reads = rt;
  }
#endif /* OPERATION_LOGGING == OPLOG_FULL */

  return r;
}

static INLINE w_entry_unique_t *
stm_add_to_ws_unique(stm_tx_t *tx, stm_word_t *addr) {
  w_entry_unique_t *wu;
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  stm_write_unique_t wut;
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */

  /* Add address to write set */
  if (unlikely(tx->w_set_unique.nb_entries == tx->w_set_unique.size)) {
    if (tx->w_set_unique.nb_acquired > 0)
      stm_rollback(tx, STM_ABORT_EXTEND_WS);
    else
      stm_allocate_ws_unique_entries(tx, 1);
  }
#if WRITE_SET_UNIQUE == RW_ADAPTIVE
  else if (!kh_size(tx->w_set_unique.hash) && tx->w_set_unique.nb_entries == RW_ADAPTIVE_THRESHOLD) {
    /* Reached the threshold; add all entries to the hash table */
    for (wut.idx = WRITE_RESERVED_IDX + 1; wut.idx < tx->w_set_unique.nb_entries; ++wut.idx) {
      int ret;
      assert(wut.idx != WRITE_RESERVED_IDX);
      kh_put(w_set_unique, tx->w_set_unique.hash, wut, &ret);
# if DESIGN == WRITE_BACK_CTL
      assert(ret > 0);
# elif DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_THROUGH
      assert(ret >= 0);
# else
#  error "Unsupported"
# endif /* DETECTION */
    }
  }
#endif /* WRITE_SET_UNIQUE == RW_ADAPTIVE */

  wu = &tx->w_set_unique.entries[tx->w_set_unique.nb_entries++];
  assert(WRITE_UNIQUE_POINTER_VALID(tx, wu));
  wu->addr = addr;
#if DETECTION == TIME_BASED
  wu->lock = GET_LOCK(addr);
#endif /* DETECTION == TIME_BASED */
  wu->latest.idx = STM_BAD_IDX;
#if DETECTION == TIME_BASED
  wu->version = 0;
#endif /* DETECTION == TIME_BASED */
#if DESIGN == WRITE_BACK_CTL
  wu->no_drop = 1;
#endif /* DESIGN == WRITE_BACK_CTL */

#ifdef USE_BLOOM_FILTER
  tx->w_set_unique.bloom |= FILTER_BITS(addr);
#endif /* USE_BLOOM_FILTER */

#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  if (
# if WRITE_SET_UNIQUE == RW_ADAPTIVE
    kh_size(tx->w_set_unique.hash)
# else
    1
# endif /* WRITE_SET_UNIQUE == RW_ADAPTIVE */
  ) {
    int ret;
    assert(wu != &tx->w_set_unique.entries[WRITE_RESERVED_IDX]);
    wut = WRITE_UNIQUE_FROM_POINTER(tx, wu);
    kh_put(w_set_unique, tx->w_set_unique.hash, wut, &ret);
    assert(ret > 0);
  }
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */

  return wu;
}

static INLINE stm_tx_policy_t stm_conflict_get_decision(stm_tx_t *tx, const tx_conflict_t *conflict)
{
  PRINT_DEBUG("==> stm_conflict_get_decision(%p[%lu],%u,0x%lx,0x%lx)\n", tx, (unsigned long)tx->end, conflict->entries.type, conflict->entries.e1, conflict->entries.e2);

#ifdef CONFLICT_TRACKING
  if (unlikely(_tinystm.conflict_cb != NULL)) {
    return _tinystm.conflict_cb(tx, conflict);
  }
#endif /* CONFLICT_TRACKING */

#if CM != CM_MERGE && defined(MERGE_LOCK_CONFLICT)
  if ((conflict->entries.type == STM_RW_CONFLICT || conflict->entries.type == STM_WW_CONFLICT) && tx->w_set_unique.nb_acquired > 0) {
# if !defined(MERGE_UNLOCK) && (DETECTION == TIME_BASED)
    tx->revalidate |= REVALIDATE_RELOCK;
# endif /* !MERGE_UNLOCK && (DETECTION == TIME_BASED) */
    int_stm_unlock(tx);
    return STM_RETRY;
  }
#endif /* CM != CM_MERGE && MERGE_LOCK_CONFLICT */

#if CM == CM_RESTART
  return STM_KILL_SELF;
#elif CM == CM_AGGRESSIVE
  return STM_KILL_OTHER;
#elif CM == CM_DELAY
  return STM_KILL_SELF | STM_DELAY;
#elif CM == CM_TIMESTAMP
  return cm_timestamp(tx, conflict);
#elif CM == CM_BACKOFF
  return cm_backoff(tx, conflict);
#elif CM == CM_KARMA
  return cm_karma(tx, conflict);
#elif CM == CM_MERGE
  return cm_merge(tx, conflict);
#endif /* CM */
}

static stm_tx_policy_t
stm_conflict_handle_all(stm_tx_t *tx, const tx_conflict_t *conflict)
{
  PRINT_DEBUG("==> stm_conflict_handle_all(%p[%lu],%u,0x%lx,0x%lx)\n", tx, (unsigned long)tx->end, conflict->entries.type, conflict->entries.e1, conflict->entries.e2);

  stm_tx_policy_t decision = stm_conflict_handle(tx, conflict);
  if (decision == STM_KILL_SELF) {
    stm_rollback(tx, STM_ABORT_IMPLICIT | (conflict->entries.type << 8));
  }
  return decision;
}

static stm_tx_policy_t
stm_decision_kill_other(stm_tx_t *tx, const tx_conflict_t *conflict, stm_tx_policy_t decision)
{
  PRINT_DEBUG("==> stm_decision_kill_other(%p[%lu],%p,%x)\n", tx, (unsigned long)tx->end, conflict, decision);

#ifdef TRANSACTION_OPERATIONS
  if (decision == STM_KILL_OTHER) {
    assert(conflict->status);
    /* FIXME: Need to implement for CTL and WT */
    if (!stm_kill(tx, conflict->other, conflict->status))
      decision = STM_RETRY;
  }
#endif /* TRANSACTION_OPERATIONS */
  return decision;
}

static stm_tx_policy_t
stm_decision_implement(stm_tx_t *tx, const tx_conflict_t *conflict, stm_tx_policy_t decision)
{
  PRINT_DEBUG("==> stm_decision_implement(%p[%lu],%p,%x)\n", tx, (unsigned long)tx->end, conflict, decision);

#ifdef TRANSACTION_OPERATIONS
  if (GET_STATUS(tx->status) == TX_KILLING) {
    stm_rollback(tx, STM_ABORT_KILLED);
    return STM_KILL_SELF;
  }
#endif /* TRANSACTION_OPERATIONS */

  if ((decision & STM_DELAY) != 0) {
    decision = decision & ~STM_DELAY;

    /* Track the contended lock */
#ifdef CONTENDED_LOCK_TRACKING
    assert(conflict->lock);
    ATOMIC_STORE_REL(&tx->c_lock, conflict->lock);
#endif /* CONTENDED_LOCK_TRACKING */

    if ((decision & STM_RETRY) != 0) {
#ifdef CONTENDED_LOCK_TRACKING
      while (LOCK_GET_OWNED(LOCK_READ_ACQ(conflict->lock))) {
        /* Check other transaction is not waiting to avoid cyclic livelock. */
        if (ATOMIC_LOAD_ACQ(&conflict->other->c_lock)) {
          decision = STM_KILL_SELF;
          break;
        }
      }
      /* Only track the lock while waiting when retrying */
      ATOMIC_STORE_REL(&tx->c_lock, NULL);
#endif /* CONTENDED_LOCK_TRACKING */
    }
  }

  return stm_decision_kill_other(tx, conflict, decision);
}

static stm_tx_policy_t
stm_conflict_handle(stm_tx_t *tx, const tx_conflict_t *conflict)
{
  PRINT_DEBUG("==> stm_conflict_handle(%p[%lu],%u,0x%lx,0x%lx)\n", tx, (unsigned long)tx->end, conflict->entries.type, conflict->entries.e1, conflict->entries.e2);

  stm_tx_policy_t decision = stm_conflict_get_decision(tx, conflict);

  PRINT_DEBUG("==> stm_conflict_handle: %x\n", decision);

  /* Implement the conflict resolution policy */
  return stm_decision_implement(tx, conflict, decision);
}

#ifdef READ_SET_ORDERED
/* Find the previous read of the specified entry, or the last read of the specified operation */
static INLINE stm_read_t
int_stm_load_prev(const struct stm_tx *tx
# if OPERATION_LOGGING == OPLOG_FULL
  , const stm_op_t cop
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  , const stm_read_t rt) {
  stm_read_t prev;
  const op_entry_t *e = NULL;
  const unsigned int ordered = tx->attr.read_set_ordered;

  /* The first read has no previous read */
  if ((ordered ? STM_SAME_READ(rt, tx->r_set.head) : rt.idx) ==
# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
    READ_RESERVED_IDX + 1
# else
    0
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
  )
    return STM_INVALID_READ;

  /* The immediate predecessor is typically the previous read, so just probe it directly */
  if (READ_VALID_FAST(tx, rt)) {
    prev.idx = rt.idx - 1;
    if (!ordered) {
      while (READ_VALID_FAST(tx, prev)) {
        r_entry_t *r = POINTER_FROM_READ(tx, prev);
        if (r->lock)
          return prev;
        --prev.idx;
      }

      return STM_INVALID_READ;
    } else {
      r_entry_t *r = POINTER_FROM_READ(tx, prev);
      if (STM_SAME_READ(r->next, rt) && r->lock)
        return prev;
    }
  }

  /* Either the specified operation has no reads, or the immediate predecessor is not the previous read, so need to search through the operation log */
# if OPERATION_LOGGING == OPLOG_FULL
  stm_op_t op = cop;
  assert(!READ_VALID(tx, rt) || STM_SAME_OP(op, POINTER_FROM_READ(tx, rt)->op));
  /* Search through the reads of each operation */
  while (1) {
    if (OP_VALID(tx, op)) {
      e = GET_LOG_ENTRY(tx, op.idx);
      if (e->status == OP_STATUS_REVERTED || STM_SAME_READ(e->reads, rt))
        goto parent;

      /* Valid parent operation */
      prev = e->reads;
    } else {
# endif /* OPERATION_LOGGING == OPLOG_FULL */
      /* Ensure that the whole read set is searched if we are at the top level */
      prev.idx = ordered ? tx->r_set.head.idx :
# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
        READ_RESERVED_IDX + 1
# else
        0
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
        ;
# if OPERATION_LOGGING == OPLOG_FULL
    }
# endif /* OPERATION_LOGGING == OPLOG_FULL */

    /* Iterate until the matching read is found */
    while (READ_VALID_FAST(tx, prev)) {
      const r_entry_t *r = POINTER_FROM_READ(tx, prev);
      if (ordered)
        assert(r->lock);
      else if (!r->lock)
        continue;

# if OPERATION_LOGGING == OPLOG_FULL
      /* Reached the end of the current operation's reads */
      if (OP_VALID(tx, r->op) && !STM_SAME_OP(r->op, op) && (!OP_SUBTREE(op.idx, r->op) || (ordered && !READ_VALID_FAST(tx, r->next)))) {
        /* Found the predecessor from the previous operation */
        if (!READ_VALID_FAST(tx, rt))
          return prev;
        else if (OP_VALID(tx, op))
          break;
      }
# endif /* OPERATION_LOGGING == OPLOG_FULL */
      /* Found the predecessor */
      if (READ_VALID_FAST(tx, rt) && STM_SAME_READ(rt, ordered ? r->next : READ_FROM_POINTER(tx, r + 1)))
        return prev;
      assert(!STM_SAME_READ(prev, ordered ? r->next : READ_FROM_POINTER(tx, r + 1)));
      prev = ordered ? r->next : READ_FROM_POINTER(tx, r + 1);
    }

# if OPERATION_LOGGING == OPLOG_FULL
    if (e) {
parent:
      assert(!STM_SAME_OP(op, e->parent));
      op = e->parent;
    } else
      break;
  }
# endif /* OPERATION_LOGGING == OPLOG_FULL */

  abort();
}
#endif /* READ_SET_ORDERED */

# if OPERATION_LOGGING == OPLOG_FULL
/* Find the next read of the operation, optionally with the same operation and/or address */
static INLINE stm_read_t
int_stm_load_next(const struct stm_tx *tx, const stm_read_t crt, const int op, const int addr) {
  assert(READ_VALID(tx, crt));
  const r_entry_t *r = POINTER_FROM_READ(tx, crt);
#  ifdef READ_SET_ORDERED
  const unsigned int ordered = tx->attr.read_set_ordered;
#  else
  const unsigned int ordered = 0;
#  endif /* READ_SET_ORDERED */
  assert(OP_VALID(tx, r->op));
  assert(r->lock);

#  ifdef READ_SET_ORDERED
  stm_read_t next = ordered ? r->next : READ_FROM_POINTER(tx, r + 1);
#  else
  stm_read_t next = READ_FROM_POINTER(tx, r + 1);
#  endif /* READ_SET_ORDERED */
  while (READ_VALID_FAST(tx, next)) {
    const r_entry_t *r2 = POINTER_FROM_READ(tx, next);
    if (ordered || r2->lock) {
      if (!op || STM_SAME_OP(r->op, r2->op)) {
#  ifdef READ_SET_DETAILED
        if (!addr || r->addr == r2->addr)
#  endif /* READ_SET_DETAILED */
          return READ_FROM_POINTER(tx, r2);
      } else if (OP_VALID(tx, r2->op) && !OP_SUBTREE(r->op.idx, r2->op))
        return STM_INVALID_READ;
      assert(!STM_SAME_READ(next, r2->next));
    }
#  ifdef READ_SET_ORDERED
    next = ordered ? r2->next : READ_FROM_POINTER(tx, r2 + 1);
#  else
    next = READ_FROM_POINTER(tx, r2 + 1);
#  endif /* READ_SET_ORDERED */
  }

  return STM_INVALID_READ;
}

/* Find the last read of the operation */
static INLINE stm_read_t
int_stm_load_last(struct stm_tx *tx, const stm_read_t crt) {
  assert(READ_VALID(tx, crt));
  const r_entry_t *r = POINTER_FROM_READ(tx, crt);
#  ifdef READ_SET_ORDERED
  const unsigned int ordered = tx->attr.read_set_ordered;
#  else
  const unsigned int ordered = 0;
#  endif /* READ_SET_ORDERED */
  assert(OP_VALID(tx, r->op));
  assert(r->lock);


#  ifdef READ_SET_ORDERED
  stm_read_t prev = crt, next = ordered ? r->next : READ_FROM_POINTER(tx, r + 1);
#  else
  stm_read_t prev = crt, next = READ_FROM_POINTER(tx, r + 1);
#  endif /* READ_SET_ORDERED */
  while (READ_VALID_FAST(tx, next)) {
    const r_entry_t *r2 = POINTER_FROM_READ(tx, next);
    if (ordered || r2->lock) {
      if (STM_SAME_OP(r->op, r2->op))
        prev = next;
      else if (OP_VALID(tx, r2->op) && !OP_SUBTREE(r->op.idx, r2->op))
        break;
      assert(!STM_SAME_READ(next, r2->next));
    }
#  ifdef READ_SET_ORDERED
    next = ordered ? r2->next : READ_FROM_POINTER(tx, r2 + 1);
#  else
    next = READ_FROM_POINTER(tx, r2 + 1);
#  endif /* READ_SET_ORDERED */
  }

  return prev;
}
# endif /* OPERATION_LOGGING == OPLOG_FULL */

#if OPERATION_LOGGING == OPLOG_FULL
/* Find the previous write to the same address in the specified operation */
static INLINE stm_write_t
int_stm_store_prev(const struct stm_tx *tx, const stm_write_t wt, const stm_op_t op) {
  assert(WRITE_VALID(tx, wt));

  stm_write_t wtprev = wt;
  while (WRITE_VALID_FAST(tx, wtprev)) {
    const w_entry_t *wprev = POINTER_FROM_WRITE(tx, wtprev);
    assert(wprev->mask);
    /* Matching entry found */
    if (STM_SAME_OP(wprev->op, op))
      return wtprev;
    /* Reached the end of writes for the specified operation */
    if (wprev->op_next.idx <= op.idx)
      break;
    assert(!STM_SAME_WRITE(wtprev, wprev->addr_prev));
    wtprev = wprev->addr_prev;
  }

  return STM_INVALID_WRITE;
}

/* Find the latest write to the same address before the specified operation */
static INLINE w_entry_t *
int_stm_store_latest(const struct stm_tx *tx, const stm_write_t wt, const stm_op_t op) {
  w_entry_t *w = WRITE_VALID_FAST(tx, wt) ? POINTER_FROM_WRITE(tx, wt) : NULL;
  while (w && w->op_next.idx > op.idx) {
    assert(w->mask == ~(stm_word_t)0);
    w = WRITE_VALID_FAST(tx, w->addr_prev) ? POINTER_FROM_WRITE(tx, w->addr_prev) : NULL;
    assert(!w || w->mask == ~(stm_word_t)0);
  }
  return w;
}

/* Find the successor of the latest write to the same address before the specified operation */
static INLINE stm_write_t *
int_stm_store_latest2(const struct stm_tx *tx, stm_write_t *wt, const stm_op_t op) {
  assert(wt);
  stm_write_t *wtnext = wt, *wtprev = wt;
  while (WRITE_VALID_FAST(tx, *wtnext)) {
    w_entry_t *wnext = POINTER_FROM_WRITE(tx, *wtnext);
    assert(OP_VALID(tx, wnext->op));
    assert(wnext->mask);
    /* Reached the end of writes for the specified operation */
    if (wnext->op_next.idx <= op.idx)
      return wtprev;
    wtprev = wtnext;
    assert(!STM_SAME_WRITE(*wtnext, wnext->addr_prev));
    wtnext = &wnext->addr_prev;
  }

  return wtnext;
}

/* Find the next write to the same address */
static INLINE stm_write_t
int_stm_store_next(const struct stm_tx *tx, const w_entry_t *w) {
  assert(WRITE_POINTER_VALID(tx, w));
  assert(w->mask);

  /* Check if the current write is the latest write to this address */
  const stm_write_t wt = WRITE_FROM_POINTER(tx, w);
  stm_write_t current = POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->latest;
  if (!WRITE_VALID_FAST(tx, current) || STM_SAME_WRITE(wt, current))
    return STM_INVALID_WRITE;

  /* Iterate until the matching write is found */
  while (WRITE_VALID_FAST(tx, current)) {
    const w_entry_t *w2 = POINTER_FROM_WRITE(tx, current);
    assert(w2->mask);
    if (STM_SAME_WRITE(w2->addr_prev, wt))
      return current;
    assert(!STM_SAME_WRITE(current, w2->addr_prev));
    current = w2->addr_prev;
  }

  return STM_INVALID_WRITE;
}
#endif /* OPERATION_LOGGING == OPLOG_FULL */

#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
# include "stm_wbetl.h"
#elif DESIGN == WRITE_BACK_CTL
# include "stm_wbctl.h"
#elif DESIGN == WRITE_THROUGH
# include "stm_wt.h"
#elif DESIGN == MODULAR
# include "stm_wbetl.h"
# include "stm_wbctl.h"
# include "stm_wt.h"
#endif /* DESIGN == MODULAR */

#ifdef TRANSACTION_OPERATIONS
/*
 * Kill other transaction.
 */
static NOINLINE int
stm_kill(stm_tx_t *tx, stm_tx_t *other, const stm_word_t status)
{
  stm_word_t c, t;

  PRINT_DEBUG("==> stm_kill(%p[%lu],%p,s=%d)\n", tx, (unsigned long)tx->end, other, status);

# ifdef CONFLICT_TRACKING
  if (_tinystm.conflict_cb != NULL) {
    tx_conflict_t conflict = {
      .entries.type = STM_KILLED,
      .entries.e1 = ENTRY_INVALID,
      .entries.e2 = ENTRY_INVALID,
#  ifdef CONFLICT_TRACKING
      .other = other,
      .status = other->status,
#  endif /* CONFLICT_TRACKING */
#  ifdef CONTENDED_LOCK_TRACKING
      .lock = NULL,
#  endif /* CONTENDED_LOCK_TRACKING */
    };

    _tinystm.conflict_cb(tx, &conflict);
  }
# endif /* CONFLICT_TRACKING */

# ifdef IRREVOCABLE_ENABLED
  if (GET_STATUS(status) == TX_IRREVOCABLE)
    return 0;
# endif /* IRREVOCABLE_ENABLED */
  if (GET_STATUS(status) == TX_ABORTED || GET_STATUS(status) == TX_COMMITTED || GET_STATUS(status) == TX_KILLING || GET_STATUS(status) == TX_IDLE)
    return 0;
  if (GET_STATUS(status) == TX_ABORTING || GET_STATUS(status) == TX_COMMITTING) {
    /* Transaction is already aborting or committing: wait */
    while (other->status == status)
      ;
    return 0;
  }
  assert(IS_ACTIVE(status));
  /* Set status to KILLED */
  if (UPDATE_STATUS(other->status, status, status + TX_KILLING) == 0) {
    /* Transaction is committing/aborting (or has committed/aborted) */
    c = GET_STATUS_COUNTER(status);
    do {
      t = other->status;
# ifdef IRREVOCABLE_ENABLED
      if (GET_STATUS(t) == TX_IRREVOCABLE)
        return 0;
# endif /* IRREVOCABLE_ENABLED */
    } while (GET_STATUS(t) != TX_ABORTED && GET_STATUS(t) != TX_COMMITTED && GET_STATUS(t) != TX_KILLING && GET_STATUS(t) != TX_IDLE && GET_STATUS_COUNTER(t) == c);
    return 0;
  }
  /* We have killed the transaction: we can steal the lock */
  return 1;
}

/*
 * Drop locks after having been killed.
 */
static NOINLINE void
stm_drop(stm_tx_t *tx)
{
  w_entry_unique_t *wu;
  stm_version_t l;
  int i;

  PRINT_DEBUG("==> stm_drop(%p[%lu])\n", tx, (unsigned long)tx->end);

  /* Drop locks */
  i = tx->w_set_unique.nb_entries;
  if (i > 0) {
# if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
    wu = tx->w_set_unique.entries + WRITE_RESERVED_IDX + 1;
    for (; i > WRITE_RESERVED_IDX + 1; i--, wu++)
# else
    wu = tx->w_set_unique.entries;
    for (; i > 0; i--, wu++)
# endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
    {
      assert(wu->lock);
      l = LOCK_READ_ACQ(wu->lock);
      if (LOCK_GET_OWNED(wu->addr, l) && (w_entry_unique_t *)LOCK_GET_ADDR(l) == wu) {
        /* Drop using CAS */
        LOCK_WRITE_CAS(wu->lock, l, LOCK_SET_TIMESTAMP(wu->version));
        /* If CAS fail, lock has been stolen or already released in case a lock covers multiple addresses */
      }
    }
    /* We need to reallocate the write set to avoid an ABA problem (the
     * transaction could reuse the same entry after having been killed
     * and restarted, and another slow transaction could steal the lock
     * using CAS without noticing the restart) */
    gc_free(tx->w_set_unique.entries, GET_CLOCK, 0);
    stm_allocate_ws_unique_entries(tx, 0);
  }
}
#endif /* TRANSACTION_OPERATIONS */

/*
 * Initialize the transaction descriptor before start or restart.
 */
static INLINE void
int_stm_prepare(stm_tx_t *tx)
{
  stm_version_t t;
#if DESIGN == WRITE_BACK_ETL_VR
  if (tx->attr.visible_reads || (tx->visible_reads >= _tinystm.vr_threshold && _tinystm.vr_threshold >= 0)) {
    /* Use visible read */
    tx->attr.visible_reads = 1;
    tx->attr.read_only = 0;
  }
#endif /* DESIGN == WRITE_BACK_ETL */

#if !defined(MERGE_UNLOCK) && (CM == CM_MERGE || defined(MERGE_LOCK_CONFLICT)) && (DETECTION == TIME_BASED)
  tx->revalidate = REVALIDATE_NONE;
#endif /* !MERGE_UNLOCK && (CM == CM_MERGE || MERGE_LOCK_CONFLICT) && (DETECTION == TIME_BASED) */

  /* Read/write set */
#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
  kh_clear(r_set, tx->r_set.hash);
  tx->r_set.nb_entries = READ_RESERVED_IDX + 1;
#else
  tx->r_set.nb_entries = 0;
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
#ifdef READ_SET_ORDERED
  tx->r_set.head = STM_INVALID_READ;
  tx->r_set.tail = STM_INVALID_READ;
  tx->r_set.free = STM_INVALID_READ;
#endif /* READ_SET_ORDERED */
#ifdef USE_BLOOM_FILTER
  tx->w_set_unique.bloom = 0;
#endif /* USE_BLOOM_FILTER */
#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
  kh_clear(w_set, tx->w_set.hash);
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  kh_clear(w_set_unique, tx->w_set_unique.hash);
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE || WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  tx->w_set.entries[WRITE_RESERVED_IDX].unique = WRITE_UNIQUE_FROM_POINTER(tx, &tx->w_set_unique.entries[WRITE_RESERVED_IDX]);
  tx->w_set.nb_entries = WRITE_RESERVED_IDX + 1;
  tx->w_set_unique.nb_entries = WRITE_RESERVED_IDX + 1;
#else
  tx->w_set.nb_entries = 0;
  tx->w_set_unique.nb_entries = 0;
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE || WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
  /* has_writes / nb_acquired are the same field. */
  tx->w_set_unique.has_writes = 0;
#if OPERATION_LOGGING != OPLOG_NONE
  tx->op_current = STM_INVALID_OP;
  tx->op_log.used = 0;
#endif /* OPERATION_LOGGING */
#if CM == CM_MERGE
# ifdef MERGE_FEEDBACK
  memset(tx->feedback, 0, sizeof(tx->feedback));
# endif /* MERGE_FEEDBACK */
# if OPERATION_LOGGING == OPLOG_FULL
  tx->op_mergeable_delayed = 0;
#  ifdef MERGE_JIT
  tx->op_mergeable_jit = 0;
#  endif /* MERGE_JIT */
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  tx->merge = NULL;
# ifdef TM_STATISTICS
  tx->stat_merges_manual = 0;
#  if OPERATION_LOGGING == OPLOG_FULL
  tx->stat_merges_replay = 0;
#  endif /* OPERATION_LOGGING */
  tx->stat_merges_ok = 0;
  tx->stat_merges_retry = 0;
  tx->stat_reverted_reads = 0;
  tx->stat_reverted_writes = 0;
  tx->stat_reverted_ops = 0;
# endif /* TM_STATISTICS */
#endif /* CM == CM_MERGE */
#ifdef TM_STATISTICS2
  tx->stat_work = get_time();
  tx->stat_work_merge = 0;
#endif /* TM_STATISTICS2 */

start:
  t = GET_CLOCK;
  /* Start timestamp */
  tx->end = t; /* OPT: Could be delayed until first read/write */
  if (unlikely(t >= VERSION_MAX)) {
    /* Block all transactions and reset clock */
    stm_quiesce_barrier(tx, rollover_clock, NULL);
    goto start;
  }

#if CM == CM_TIMESTAMP
  if (tx->stat_retries == 0)
    tx->timestamp = t;
#endif /* CM == CM_TIMESTAMP */

#if MEMORY_MANAGEMENT != MM_NONE
  gc_set_epoch(t);
#endif /* MEMORY_MANAGEMENT */

#ifdef IRREVOCABLE_ENABLED
  if (unlikely(tx->irrevocable != 0)) {
    assert(!IS_ACTIVE(tx->status));
    stm_set_irrevocable_tx(tx, -1);
    UPDATE_STATUS_RAW(tx->status, TX_IRREVOCABLE);
  } else
    UPDATE_STATUS_RAW(tx->status, TX_ACTIVE_BIT);
#else /* ! IRREVOCABLE_ENABLED */
  /* Set status */
  UPDATE_STATUS_RAW(tx->status, TX_ACTIVE_BIT);
#endif /* ! IRREVOCABLE_ENABLED */

  stm_check_quiesce(tx);
}

static INLINE int
int_stm_revalidate(struct stm_tx *tx) {
  PRINT_DEBUG("==> stm_revalidate(%p[%lu])\n", tx, (unsigned long)tx->end);

#if DETECTION == TIME_BASED
  stm_version_t t = GET_CLOCK;
#endif /* DETECTION == TIME_BASED */
#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
  return stm_wbetl_extend(tx
# if DETECTION == TIME_BASED
    , t
# endif /* DETECTION == TIME_BASED */
  );
#elif DESIGN == WRITE_BACK_CTL
  return stm_wbctl_extend(tx
# if DETECTION == TIME_BASED
    , t
# endif /* DETECTION == TIME_BASED */
  );
#elif DESIGN == WRITE_THROUGH
  return stm_wt_extend(tx
# if DETECTION == TIME_BASED
    , t
# endif /* DETECTION == TIME_BASED */
  );
#elif DESIGN == MODULAR
  if (tx->attr.id == WRITE_BACK_ETL || tx->attr.id == WRITE_BACK_ETL_VR)
    return stm_wbetl_extend(tx
# if DETECTION == TIME_BASED
      , t
# endif /* DETECTION == TIME_BASED */
    );
  else if (tx->attr.id == WRITE_BACK_CTL)
    return stm_wbctl_extend(tx
# if DETECTION == TIME_BASED
      , t
# endif /* DETECTION == TIME_BASED */
    );
  else if (tx->attr.id == WRITE_THROUGH)
    return stm_wt_extend(tx
# if DETECTION == TIME_BASED
    , t
# endif /* DETECTION == TIME_BASED */
    );
#else
# error "Unsupported"
#endif /* DESIGN == MODULAR */
}

static INLINE void
int_stm_unlock(struct stm_tx *tx) {
  PRINT_DEBUG("==> stm_unlock(%p[%lu])\n", tx, (unsigned long)tx->end);

#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
  stm_wbetl_rollback(tx);
#elif DESIGN == WRITE_BACK_CTL
  stm_wbctl_rollback(tx);
  assert(tx->w_set_unique.nb_acquired == 0);
#elif DESIGN == WRITE_THROUGH
  stm_wt_rollback(tx);
#elif DESIGN == MODULAR
  if (tx->attr.id == WRITE_BACK_CTL) {
    stm_wbctl_rollback(tx);
    assert(tx->w_set_unique.nb_acquired == 0);
  } else if (tx->attr.id == WRITE_THROUGH)
    stm_wt_rollback(tx);
  else
    stm_wbetl_rollback(tx);
#endif /* DESIGN == MODULAR */
}

static INLINE void stm_cleanup(stm_tx_t *tx, stm_tx_abort_t reason)
{
#if CM == CM_BACKOFF
  unsigned long wait;
  int j;
#endif /* CM == CM_BACKOFF */
#ifdef TRANSACTION_OPERATIONS
  stm_word_t t;
#endif /* TRANSACTION_OPERATIONS */

  PRINT_DEBUG("==> stm_cleanup(%p[%lu])\n", tx, (unsigned long)tx->end);

  assert(IS_ACTIVE(tx->status));

#ifdef DEBUG_ABORT
  if (!debug)
    debug = debug_begin();

  const char *file;
  int row, col;
  char stack[512] = {'\0'}, source[256] = {'\0'};
  for (unsigned i = 0; i <= 5; ++i) {
    pthread_mutex_lock(&mutex);
    if (!debug_source_location(debug, i, &file, &row, &col))
      snprintf(source, sizeof(source), "%s:%d:%d ", file, row, col);
    pthread_mutex_unlock(&mutex);
    strcat(stack, source);
  }
  printf("==> abort: %s\n", stack);
#endif /* DEBUG_ABORT */

#ifdef IRREVOCABLE_ENABLED
  /* Irrevocable cannot abort */
  assert((tx->irrevocable & 0x07) != 3);
#endif /* IRREVOCABLE_ENABLED */

#ifdef TRANSACTION_OPERATIONS
  /* Set status to ABORTING */
  t = tx->status;
  if (GET_STATUS(t) == TX_KILLING || (IS_ACTIVE(t) && UPDATE_STATUS(tx->status, t, t + TX_ABORTED) == 0)) {
    /* We have been killed */
    assert(GET_STATUS(tx->status) == TX_KILLING);
    /* Release locks */
    stm_drop(tx);
    goto dropped;
  }
#endif /* TRANSACTION_OPERATIONS */

  int_stm_unlock(tx);

#ifdef TRANSACTION_OPERATIONS
 dropped:
#endif /* TRANSACTION_OPERATIONS */

#ifdef TM_STATISTICS
  tx->stat_aborts++;
  tx->stat_retries++;
  if (tx->stat_retries_max < tx->stat_retries)
    tx->stat_retries_max = tx->stat_retries;
#endif /* TM_STATISTICS */
#ifdef TM_STATISTICS2
  /* Aborts stats wrt reason */
  if (reason & STM_ABORT_IMPLICIT)
    tx->stat_aborts_r[(reason & ~STM_ABORT_IMPLICIT) >> 8]++;
  else if (reason & STM_ABORT_EXPLICIT)
    tx->stat_aborts_r[STM_EXPLICIT]++;
  if (tx->stat_retries == 1)
    tx->stat_aborts_1++;
  else if (tx->stat_retries == 2)
    tx->stat_aborts_2++;
#endif /* TM_STATISTICS2 */

  /* Set status to ABORTED */
  SET_STATUS(tx->status, TX_ABORTED);

  /* Abort for extending the write set */
  if (unlikely(reason == STM_ABORT_EXTEND_WS)) {
    stm_allocate_ws_unique_entries(tx, 1);
  }

  /* Reset nesting level */
  tx->nesting = 0;

#  if CM == CM_MERGE && defined(MERGE_FEEDBACK)
  for (unsigned int i = 0; i < _tinystm.op_info.nb_ids; ++i) {
    if (tx->feedback[i])
      ATOMIC_FETCH_INC_FULL(&_tinystm.op_info.ids[i].aborted_tx);
  }
#  endif /* CM == CM_MERGE && MERGE_FEEDBACK */

  /* Callbacks */
  if (likely(_tinystm.nb_abort_cb != 0)) {
    for (unsigned int cb = 0; cb < _tinystm.nb_abort_cb; cb++)
      _tinystm.abort_cb[cb].f(tx, reason, _tinystm.abort_cb[cb].arg);
  }

#if CM == CM_BACKOFF
  /* Simple RNG (good enough for backoff) */
  tx->seed ^= (tx->seed << 17);
  tx->seed ^= (tx->seed >> 13);
  tx->seed ^= (tx->seed << 5);
  wait = tx->seed % tx->backoff;
  for (j = 0; j < wait; j++) {
    /* Do nothing */
  }
  if (tx->backoff < MAX_BACKOFF)
    tx->backoff <<= 1;
#endif /* CM == CM_BACKOFF */

#ifdef CONTENDED_LOCK_TRACKING
  const stm_lock_t *l = (stm_lock_t *)ATOMIC_LOAD_ACQ(&tx->c_lock);
  /* Wait until contented lock is free */
  if (l != NULL) {
    /* Busy waiting (yielding is expensive) */
    while (LOCK_GET_OWNED(LOCK_READ(l))) {
# ifdef WAIT_YIELD
      sched_yield();
# endif /* WAIT_YIELD */
    }
    ATOMIC_STORE_REL(&tx->c_lock, NULL);
  }
#endif /* CONTENDED_LOCK_TRACKING */
}

/*
 * Rollback transaction.
 */
static NOINLINE void
stm_rollback(stm_tx_t *tx, stm_tx_abort_t reason)
{
  PRINT_DEBUG("==> stm_rollback(%p[%lu])\n", tx, (unsigned long)tx->end);

  stm_cleanup(tx, reason);

  /* Don't prepare a new transaction if no retry. */
  if (tx->attr.no_retry || (reason & STM_ABORT_NO_RETRY) == STM_ABORT_NO_RETRY)
    return;

  /* Reset nesting level */
  tx->nesting = 1;

  /* Reset field to restart transaction */
  int_stm_prepare(tx);

  /* Jump back to transaction start */
  /* Note: ABI usually requires 0x09 (runInstrumented+restoreLiveVariable) */
#ifdef IRREVOCABLE_ENABLED
  /* If the transaction is serial irrevocable, indicate that uninstrumented
   * code path must be executed (mixing instrumented and uninstrumented
   * accesses are not allowed) */
  reason |= (tx->irrevocable == 0x0B) ? STM_PATH_UNINSTRUMENTED : STM_PATH_INSTRUMENTED;
#else /* ! IRREVOCABLE_ENABLED */
  reason |= STM_PATH_INSTRUMENTED;
#endif /* ! IRREVOCABLE_ENABLED */

  LONGJMP(tx->env, reason);
}

/*
 * Store a word-sized value (return write set entry or NULL).
 */
static INLINE w_entry_t *
stm_write(stm_tx_t *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
  w_entry_t *w;

#ifdef TRANSACTION_OPERATIONS
  if (GET_STATUS(tx->status) == TX_KILLING) {
    stm_rollback(tx, STM_ABORT_KILLED);
    return NULL;
  }
#else /* TRANSACTION_OPERATIONS */
  assert(IS_ACTIVE(tx->status));
#endif /* TRANSACTION_OPERATIONS */

#ifdef DEBUG
  /* Check consistency with read_only attribute. */
  assert(!tx->attr.read_only);
#endif /* DEBUG */

#ifdef TM_STATISTICS2
  ++tx->stat_writes;
#endif /* TM_STATISTICS2 */

#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
  w = stm_wbetl_write(tx, addr, value, mask);
#elif DESIGN == WRITE_BACK_CTL
  w = stm_wbctl_write(tx, addr, value, mask);
#elif DESIGN == WRITE_THROUGH
  w = stm_wt_write(tx, addr, value, mask);
#elif DESIGN == MODULAR
  if (tx->attr.id == WRITE_BACK_CTL)
    w = stm_wbctl_write(tx, addr, value, mask);
  else if (tx->attr.id == WRITE_THROUGH)
    w = stm_wt_write(tx, addr, value, mask);
  else
    w = stm_wbetl_write(tx, addr, value, mask);
#endif /* DESIGN == WRITE_THROUGH */

  return w;
}

static INLINE stm_word_t
int_stm_RaR(stm_tx_t *tx, stm_word_t *addr)
{
  stm_word_t value;
#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
  value = stm_wbetl_RaR(tx, addr);
#elif DESIGN == WRITE_BACK_CTL
  value = stm_wbctl_RaR(tx, addr);
#elif DESIGN == WRITE_THROUGH
  value = stm_wt_RaR(tx, addr);
#endif /* DESIGN == WRITE_THROUGH */
  return value;
}

static INLINE stm_word_t
int_stm_RaW(stm_tx_t *tx, stm_word_t *addr)
{
  stm_word_t value;
#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
  value = stm_wbetl_RaW(tx, addr);
#elif DESIGN == WRITE_BACK_CTL
  value = stm_wbctl_RaW(tx, addr);
#elif DESIGN == WRITE_THROUGH
  value = stm_wt_RaW(tx, addr);
#endif /* DESIGN == WRITE_THROUGH */
  return value;
}

static INLINE stm_word_t
int_stm_RfW(stm_tx_t *tx, stm_word_t *addr)
{
  stm_word_t value;
#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
  value = stm_wbetl_RfW(tx, addr);
#elif DESIGN == WRITE_BACK_CTL
  value = stm_wbctl_RfW(tx, addr);
#elif DESIGN == WRITE_THROUGH
  value = stm_wt_RfW(tx, addr);
#endif /* DESIGN == WRITE_THROUGH */
  return value;
}

static INLINE void
int_stm_WaR(stm_tx_t *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
  stm_wbetl_WaR(tx, addr, value, mask);
#elif DESIGN == WRITE_BACK_CTL
  stm_wbctl_WaR(tx, addr, value, mask);
#elif DESIGN == WRITE_THROUGH
  stm_wt_WaR(tx, addr, value, mask);
#endif /* DESIGN == WRITE_THROUGH */
}

static INLINE void
int_stm_WaW(stm_tx_t *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
  stm_wbetl_WaW(tx, addr, value, mask);
#elif DESIGN == WRITE_BACK_CTL
  stm_wbctl_WaW(tx, addr, value, mask);
#elif DESIGN == WRITE_THROUGH
  stm_wt_WaW(tx, addr, value, mask);
#endif /* DESIGN == WRITE_THROUGH */
}

static INLINE stm_tx_t *
int_stm_init_thread(void)
{
  stm_tx_t *tx = NULL;

  PRINT_DEBUG("==> stm_init_thread()\n");

  /* Avoid initializing more than once */
  if (!_tinystm.initialized || (tx = tls_get_tx()) != NULL)
    return tx;

#if MEMORY_MANAGEMENT != MM_NONE
  gc_init_thread();
#endif /* MEMORY_MANAGEMENT */

  /* Allocate descriptor */
  tx = (stm_tx_t *)xmalloc_aligned(sizeof(stm_tx_t));
  /* Set attribute */
  tx->attr = (stm_tx_attr_t)0;
  /* Set status (no need for CAS or atomic op) */
  tx->status = TX_IDLE;

  /* Read set */
  tx->r_set.size = R_SET_SIZE;
#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
  tx->r_set.hash = kh_init(r_set);
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
  stm_allocate_rs_entries(tx, 0);
  /* Write set */
  tx->w_set.size = W_SET_SIZE;
#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
  tx->w_set.hash = kh_init(w_set);
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */
  stm_allocate_ws_entries(tx, 0);
  tx->w_set_unique.size = W_SET_UNIQUE_SIZE;
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  tx->w_set_unique.hash = kh_init(w_set_unique);
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
  stm_allocate_ws_unique_entries(tx, 0);
#ifdef USE_BLOOM_FILTER
  tx->w_set_unique.bloom = 0;
#endif /* USE_BLOOM_FILTER */
#if OPERATION_LOGGING != OPLOG_NONE
  /* Operation log */
  tx->op_log.size = OP_LOG_SIZE;
  stm_allocate_ol_entries(tx, 0);
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  /* Nesting level */
  tx->nesting = 0;
  /* Transaction-specific data */
  memset(tx->data, 0, MAX_SPECIFIC * sizeof(void *));
#ifdef CONFLICT_TRACKING
  /* Thread identifier */
  tx->thread_id = pthread_self();
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
  /* Contented lock */
  tx->c_lock = NULL;
#endif /* CONTENDED_LOCK_TRACKING */
#if CM == CM_BACKOFF
  /* Backoff */
  tx->backoff = MIN_BACKOFF;
  tx->seed = 123456789UL;
#endif /* CM == CM_BACKOFF */
#if DESIGN == WRITE_BACK_ETL_VR
  tx->visible_reads = 0;
#endif /* DESIGN == WRITE_BACK_ETL_VR */
#if CM == CM_TIMESTAMP
  tx->timestamp = 0;
#endif /* CM == CM_TIMESTAMP */
#ifdef TM_STATISTICS
  /* Statistics */
  tx->stat_extensions = 0;
  tx->stat_commits = 0;
  tx->stat_aborts = 0;
  tx->stat_relocks = 0;
  tx->stat_retries = 0;
  tx->stat_retries_max = 0;
#endif /* TM_STATISTICS */
#ifdef TM_STATISTICS2
  tx->stat_reads = 0;
  tx->stat_writes = 0;
  tx->stat_aborts_1 = 0;
  tx->stat_aborts_2 = 0;
  memset(tx->stat_aborts_r, 0, sizeof(unsigned int) * 16);
# ifdef READ_LOCKED_DATA
  tx->stat_locked_reads_ok = 0;
  tx->stat_locked_reads_failed = 0;
# endif /* READ_LOCKED_DATA */
  tx->stat_work = 0;
  tx->stat_work_merge = 0;
#endif /* TM_STATISTICS2 */
#ifdef IRREVOCABLE_ENABLED
  tx->irrevocable = 0;
#endif /* IRREVOCABLE_ENABLED */
  /* Store as thread-local data */
  tls_set_tx(tx);
  stm_quiesce_enter_thread(tx);

  /* Callbacks */
  if (likely(_tinystm.nb_init_cb != 0)) {
    unsigned int cb;
    for (cb = 0; cb < _tinystm.nb_init_cb; cb++)
      _tinystm.init_cb[cb].f(tx, _tinystm.init_cb[cb].arg);
  }

  return tx;
}

static INLINE void
int_stm_exit_thread(stm_tx_t *tx)
{
#if MEMORY_MANAGEMENT != MM_NONE
  stm_version_t t;
#endif /* MEMORY_MANAGEMENT */

  PRINT_DEBUG("==> stm_exit_thread(%p[%lu])\n", tx, (unsigned long)tx->end);

  /* Avoid finalizing again a thread */
  if (!_tinystm.initialized || tx == NULL)
    return;

  /* Callbacks */
  if (likely(_tinystm.nb_exit_cb != 0)) {
    unsigned int cb;
    for (cb = 0; cb < _tinystm.nb_exit_cb; cb++)
      _tinystm.exit_cb[cb].f(tx, _tinystm.exit_cb[cb].arg);
  }

  stm_quiesce_exit_thread(tx);

#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
  kh_destroy(r_set, tx->r_set.hash);
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
  kh_destroy(w_set, tx->w_set.hash);
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  kh_destroy(w_set_unique, tx->w_set_unique.hash);
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */

#if MEMORY_MANAGEMENT != MM_NONE
  t = GET_CLOCK;
# if OPERATION_LOGGING != OPLOG_NONE
  gc_free(tx->op_log.entries, t);
# endif /* OPERATION_LOGGING != OPLOG_NONE */
  gc_free(tx->r_set.entries, t);
  gc_free(tx->w_set.entries, t);
  gc_free(tx->w_set_unique.entries, t);
  gc_free(tx, t);
  gc_exit_thread();
#else /* MEMORY_MANAGEMENT == MM_NONE */
# if OPERATION_LOGGING != OPLOG_NONE
  xfree(tx->op_log.entries);
# endif /* OPERATION_LOGGING != OPLOG_NONE */
  xfree(tx->r_set.entries);
  xfree(tx->w_set.entries);
  xfree(tx->w_set_unique.entries);
  xfree(tx);
#endif /* MEMORY_MANAGEMENT */

  tls_set_tx(NULL);
}

static INLINE sigjmp_buf *
int_stm_start(stm_tx_t *tx, stm_tx_attr_t attr)
{
  PRINT_DEBUG("==> stm_start(%p)\n", tx);

  /* TODO Nested transaction attributes are not checked if they are coherent
   * with parent ones.  */

  /* Increment nesting level */
  if (tx->nesting++ > 0)
    return NULL;

  /* Attributes */
#if CM == CM_MERGE && defined(READ_SET_ORDERED)
  int temp = tx->attr.read_set_ordered;
  tx->attr = attr;
  tx->attr.read_set_ordered = temp;
#else
  tx->attr = attr;
#endif /* CM == CM_MERGE && defined(READ_SET_ORDERED) */

  /* Initialize transaction descriptor */
  int_stm_prepare(tx);

  /* Callbacks */
  if (likely(_tinystm.nb_start_cb != 0)) {
    unsigned int cb;
    for (cb = 0; cb < _tinystm.nb_start_cb; cb++)
      _tinystm.start_cb[cb].f(tx, _tinystm.start_cb[cb].arg);
  }

  return &tx->env;
}

static INLINE int
int_stm_commit(stm_tx_t *tx)
{
#ifdef TRANSACTION_OPERATIONS
  stm_word_t t;
#endif /* TRANSACTION_OPERATIONS */

  PRINT_DEBUG("==> stm_commit(%p[%lu])\n", tx, (unsigned long)tx->end);

  /* Decrement nesting level */
  if (unlikely(--tx->nesting > 0))
    return 1;

  /* Callbacks */
  if (unlikely(_tinystm.nb_precommit_cb != 0)) {
    unsigned int cb;
    for (cb = 0; cb < _tinystm.nb_precommit_cb; cb++)
      _tinystm.precommit_cb[cb].f(tx, _tinystm.precommit_cb[cb].arg);
  }

  assert(IS_ACTIVE(tx->status));

#ifdef TRANSACTION_OPERATIONS
  /* Set status to COMMITTING */
  t = tx->status;
  if (GET_STATUS(t) == TX_KILLING || UPDATE_STATUS(tx->status, t, t + (TX_COMMITTING - GET_STATUS(t))) == 0) {
    /* We have been killed */
    assert(GET_STATUS(tx->status) == TX_KILLING);
    stm_rollback(tx, STM_ABORT_KILLED);
    return 0;
  }
#else
  SET_STATUS(tx->status, TX_COMMITTING);
#endif /* TRANSACTION_OPERATIONS */

#if DETECTION == TIME_BASED
  /* A read-only transaction can commit immediately */
# if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  if (unlikely(tx->w_set_unique.nb_entries == WRITE_RESERVED_IDX + 1))
# else
  if (unlikely(tx->w_set_unique.nb_entries == 0))
# endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
    goto end;
#endif /* DETECTION == TIME_BASED */

  /* Update transaction */
#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
  stm_wbetl_commit(tx);
#elif DESIGN == WRITE_BACK_CTL
  stm_wbctl_commit(tx);
#elif DESIGN == WRITE_THROUGH
  stm_wt_commit(tx);
#elif DESIGN == MODULAR
  if (tx->attr.id == WRITE_BACK_CTL)
    stm_wbctl_commit(tx);
  else if (tx->attr.id == WRITE_THROUGH)
    stm_wt_commit(tx);
  else
    stm_wbetl_commit(tx);
#endif /* DESIGN == MODULAR */

end:
#ifdef TM_STATISTICS
  tx->stat_commits++;
#endif /* TM_STATISTICS */

#if CM == CM_BACKOFF
  /* Reset backoff */
  tx->backoff = MIN_BACKOFF;
#endif /* CM == CM_BACKOFF */

#if DESIGN == WRITE_BACK_ETL_VR
  tx->visible_reads = 0;
#endif /* DESIGN == WRITE_BACK_ETL_VR */

#ifdef IRREVOCABLE_ENABLED
  if (unlikely(tx->irrevocable)) {
    ATOMIC_STORE(&_tinystm.irrevocable, 0);
    if ((tx->irrevocable & 0x08) != 0)
      stm_quiesce_release(tx);
    tx->irrevocable = 0;
  }
#endif /* IRREVOCABLE_ENABLED */

  /* Set status to COMMITTED */
  SET_STATUS(tx->status, TX_COMMITTED);

  /* Callbacks */
  if (likely(_tinystm.nb_commit_cb != 0)) {
    unsigned int cb;
    for (cb = 0; cb < _tinystm.nb_commit_cb; cb++)
      _tinystm.commit_cb[cb].f(tx, _tinystm.commit_cb[cb].arg);
  }

#  if CM == CM_MERGE && defined(MERGE_FEEDBACK)
  for (unsigned int i = 0; i < _tinystm.op_info.nb_ids; ++i) {
    if (tx->feedback[i])
      ATOMIC_FETCH_INC_FULL(&_tinystm.op_info.ids[i].committed_tx);
  }
#  endif /* CM == CM_MERGE && MERGE_FEEDBACK */

  return 1;
}

static INLINE stm_word_t
int_stm_load(stm_tx_t *tx, const stm_word_t *addr
#ifdef READ_SET_TAGGED
  , uintptr_t tag
#endif /* READ_SET_TAGGED */
) {
#ifdef TM_STATISTICS2
  ++tx->stat_reads;
#endif /* TM_STATISTICS2 */

  assert(addr == ALIGN_ADDR(addr));
#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
  return stm_wbetl_read(tx, addr
# ifdef READ_SET_TAGGED
    , tag
# endif /* READ_SET_TAGGED */
  );
#elif DESIGN == WRITE_BACK_CTL
  return stm_wbctl_read(tx, addr
# ifdef READ_SET_TAGGED
    , tag
# endif /* READ_SET_TAGGED */
  );
#elif DESIGN == WRITE_THROUGH
  return stm_wt_read(tx, addr
# ifdef READ_SET_TAGGED
    , tag
# endif /* READ_SET_TAGGED */
  );
#elif DESIGN == MODULAR
  if (tx->attr.id == WRITE_BACK_CTL)
    return stm_wbctl_read(tx, addr
# ifdef READ_SET_TAGGED
      , tag
# endif /* READ_SET_TAGGED */
    );
  else if (tx->attr.id == WRITE_THROUGH)
    return stm_wt_read(tx, addr
# ifdef READ_SET_TAGGED
      , tag
# endif /* READ_SET_TAGGED */
    );
  else
    return stm_wbetl_read(tx, addr
# ifdef READ_SET_TAGGED
      , tag
# endif /* READ_SET_TAGGED */
    );
#endif /* DESIGN */
}

static INLINE void
int_stm_store(stm_tx_t *tx, stm_word_t *addr, stm_word_t value)
{
  assert(addr == ALIGN_ADDR(addr));
  stm_write(tx, addr, value, ~(stm_word_t)0);
}

static INLINE void
int_stm_store2(stm_tx_t *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
  assert(addr == ALIGN_ADDR(addr));
  stm_write(tx, addr, value, mask);
}

static INLINE int
int_stm_active(const stm_tx_t *tx)
{
  assert (tx != NULL);
  return IS_ACTIVE(tx->status);
}

static INLINE int
int_stm_aborted(const stm_tx_t *tx)
{
  assert (tx != NULL);
  return (GET_STATUS(tx->status) == TX_ABORTED);
}

static INLINE int
int_stm_committing(const stm_tx_t *tx)
{
  assert (tx != NULL);
  return (GET_STATUS(tx->status) == TX_COMMITTING);
}

static INLINE int
int_stm_irrevocable(const stm_tx_t *tx)
{
  assert (tx != NULL);
#ifdef IRREVOCABLE_ENABLED
  return ((tx->irrevocable & 0x07) == 3);
#else /* ! IRREVOCABLE_ENABLED */
  return 0;
#endif /* ! IRREVOCABLE_ENABLED */
}

static INLINE int
int_stm_killed(const stm_tx_t *tx)
{
  assert (tx != NULL);
  return (GET_STATUS(tx->status) == TX_KILLING);
}

static INLINE sigjmp_buf *
int_stm_get_env(stm_tx_t *tx)
{
  assert (tx != NULL);
  /* Only return environment for top-level transaction */
  return tx->nesting == 0 ? &tx->env : NULL;
}

static INLINE int
int_stm_get_stats(const stm_tx_t *tx, const stm_stats_t name, void *val)
{
  assert (tx != NULL);

  switch (name) {
    case STAT_READ_SET_SIZE:
      *(unsigned int *)val = tx->r_set.size;
      return 1;
    case STAT_READ_SET_NB_ENTRIES:
#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
      *(unsigned int *)val = tx->r_set.nb_entries - 1;
#else
      *(unsigned int *)val = tx->r_set.nb_entries;
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
      return 1;
    case STAT_WRITE_SET_SIZE:
      *(unsigned int *)val = tx->w_set.size;
      return 1;
    case STAT_WRITE_SET_NB_ENTRIES:
#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
      *(unsigned int *)val = tx->w_set.nb_entries - 1;
#else
      *(unsigned int *)val = tx->w_set.nb_entries;
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */
      return 1;
    case STAT_WRITE_SET_UNIQUE_SIZE:
      *(unsigned int *)val = tx->w_set_unique.size;
      return 1;
    case STAT_WRITE_SET_UNIQUE_NB_ENTRIES:
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
      *(unsigned int *)val = tx->w_set_unique.nb_entries - 1;
#else
      *(unsigned int *)val = tx->w_set_unique.nb_entries;
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
      return 1;
#if OPERATION_LOGGING == OPLOG_FULL
    case STAT_OP_LOG_SIZE:
      *(unsigned int *)val = tx->op_log.size;
      return 1;
    case STAT_OP_LOG_USED:
      *(unsigned int *)val = tx->op_log.used;
      return 1;
#endif /* OPERATION_LOGGING == OPLOG_FULL */
    case STAT_READ_ONLY:
      *(unsigned int *)val = tx->attr.read_only;
      return 1;
#ifdef TM_STATISTICS
    case STAT_NB_EXTENSIONS:
      *(unsigned int *)val = tx->stat_extensions;
      return 1;
    case STAT_NB_COMMITS:
      *(unsigned int *)val = tx->stat_commits;
      return 1;
    case STAT_NB_ABORTS:
      *(unsigned int *)val = tx->stat_aborts;
      return 1;
    case STAT_NB_RELOCKS:
      *(unsigned int *)val = tx->stat_relocks;
      return 1;
    case STAT_NB_RETRIES:
      *(unsigned int *)val = tx->stat_retries;
      return 1;
    case STAT_MAX_RETRIES:
      *(unsigned int *)val = tx->stat_retries_max;
      return 1;
    case STAT_AVG_ABORTS:
      *(unsigned int *)val = tx->stat_aborts / tx->stat_commits;
      return 1;
# if CM == CM_MERGE
    case STAT_NB_MERGES_MANUAL:
      *(unsigned int *)val = tx->stat_merges_manual;
      return 1;
#  if OPERATION_LOGGING == OPLOG_FULL
    case STAT_NB_MERGES_REPLAY:
      *(unsigned int *)val = tx->stat_merges_replay;
      return 1;
#  endif /* OPERATION_LOGGING */
    case STAT_NB_MERGES_OK:
      *(unsigned int *)val = tx->stat_merges_ok;
      return 1;
    case STAT_NB_MERGES_RETRY:
      *(unsigned int *)val = tx->stat_merges_retry;
      return 1;
    case STAT_NB_REVERTED_READS:
      *(unsigned int *)val = tx->stat_reverted_reads;
      return 1;
    case STAT_NB_REVERTED_WRITES:
      *(unsigned int *)val = tx->stat_reverted_writes;
      return 1;
    case STAT_NB_REVERTED_OPS:
      *(unsigned int *)val = tx->stat_reverted_ops;
      return 1;
# endif /* CM == CM_MERGE */
#endif /* TM_STATISTICS */
#ifdef TM_STATISTICS2
    case STAT_NB_READS:
      *(unsigned long *)val = tx->stat_reads;
      return 1;
    case STAT_NB_WRITES:
      *(unsigned long *)val = tx->stat_writes;
      return 1;
    case STAT_NB_ABORTS_1:
      *(unsigned int *)val = tx->stat_aborts_1;
      return 1;
    case STAT_NB_ABORTS_2:
      *(unsigned int *)val = tx->stat_aborts_2;
      return 1;
    case STAT_NB_ABORTS_REASON:
      memcpy(val, tx->stat_aborts_r, sizeof(tx->stat_aborts_r));
      return 1;
    case STAT_NB_ABORTS_LOCKED_READ:
      *(unsigned int *)val = tx->stat_aborts_r[STM_ABORT_WR_CONFLICT >> 8];
      return 1;
    case STAT_NB_ABORTS_LOCKED_WRITE:
      *(unsigned int *)val = tx->stat_aborts_r[STM_ABORT_WW_CONFLICT >> 8];
      return 1;
    case STAT_NB_ABORTS_VALIDATE_READ:
      *(unsigned int *)val = tx->stat_aborts_r[STM_ABORT_VAL_READ >> 8];
      return 1;
    case STAT_NB_ABORTS_VALIDATE_WRITE:
      *(unsigned int *)val = tx->stat_aborts_r[STM_ABORT_VAL_WRITE >> 8];
      return 1;
    case STAT_NB_ABORTS_VALIDATE_COMMIT:
      *(unsigned int *)val = tx->stat_aborts_r[STM_ABORT_VAL_COMMIT >> 8];
      return 1;
    case STAT_NB_ABORTS_KILLED:
      *(unsigned int *)val = tx->stat_aborts_r[STM_ABORT_KILLED >> 8];
      return 1;
    case STAT_NB_ABORTS_INVALID_MEMORY:
      *(unsigned int *)val = tx->stat_aborts_r[STM_ABORT_SIGNAL >> 8];
      return 1;
# ifdef READ_LOCKED_DATA
    case STAT_LOCKED_READS_OK:
      *(unsigned int *)val = tx->stat_locked_reads_ok;
      return 1;
    case STAT_LOCKED_READS_FAILED:
      *(unsigned int *)val = tx->stat_locked_reads_failed;
      return 1;
# endif /* READ_LOCKED_DATA */
      case STAT_WORK:
      *(unsigned long long *)val = tx->stat_work;
      return 1;
      case STAT_WORK_MERGE:
      *(unsigned long long *)val = tx->stat_work_merge;
      return 1;
#endif /* TM_STATISTICS2 */
    default:
      return 0;
  }
}

static INLINE void
int_stm_set_specific(stm_tx_t *tx, const int key, const void *data)
{
  assert (tx != NULL && key >= 0 && key < _tinystm.nb_specific);
  ATOMIC_STORE(&tx->data[key], data);
}

static INLINE void *
int_stm_get_specific(const stm_tx_t *tx, const int key)
{
  assert (tx != NULL && key >= 0 && key < _tinystm.nb_specific);
  return (void *)ATOMIC_LOAD(&tx->data[key]);
}

#if OPERATION_LOGGING != OPLOG_NONE
static INLINE int
int_stm_begin_op(struct stm_tx *tx, const stm_op_id_t id, const stm_merge_cb_t jit, va_list args) {
# ifdef DEBUG_OP_LOG
  PRINT_DEBUG("==> stm_begin_op(%p[%lu],0x%lx[%s],c0x%lx)\n", tx, (unsigned long)tx->end, id.idx, _tinystm.op_info.ids[id.idx].name, tx->op_current.idx);
# else
  PRINT_DEBUG("==> stm_begin_op(%p[%lu],0x%lx,c0x%lx)\n", tx, (unsigned long)tx->end, id.idx, tx->op_current.idx);
# endif /* DEBUG_OP_LOG */

  assert(IS_ACTIVE(tx->status));

  assert(OPID_VALID(id));
  if (unlikely(!OPID_VALID(id)))
    return 0;

  stm_op_t *current;
  unsigned int *next;
  unsigned int size;
# if OPERATION_LOGGING != OPLOG_FULL
  unsigned int next_entry;
# endif /* OPERATION_LOGGING != OPLOG_FULL */

# if CM == CM_MERGE && defined(MERGE_FEEDBACK)
  if (!_tinystm.op_info.ids[id.idx].enabled)
    return 1;
  ATOMIC_FETCH_INC_FULL(&_tinystm.op_info.ids[id.idx].executions);
# endif /* CM == CM_MERGE && MERGE_FEEDBACK */

  if (
# if CM == CM_MERGE
    likely(!tx->merge)
# else
    1
# endif /* CM == CM_MERGE */
  ) {
    /* Regular operation, no merging */
    current = &tx->op_current;
    next = &tx->op_log.used;
# if OPERATION_LOGGING != OPLOG_FULL
    /* Reuse an existing entry if it has been recorded before */
    stm_op_t start = { .idx = OP_VALID(tx, *current) ? current->idx : 0 };
    for (stm_op_t i = { .idx = start.idx ? start.idx + OP_ENTRY_SIZE() : start.idx }; OP_VALID(tx, i) && OP_SUBTREE(start.idx, i); i.idx += OP_ENTRY_SIZE()) {
      op_entry_t *e = GET_LOG_ENTRY(tx, i.idx);
      if (STM_SAME_OP(e->parent, *current) && STM_SAME_OPID(e->id, id)) {
        next_entry = GET_OP_IDX(i.idx);
        next = &next_entry;
        break;
      }
    }
# endif /* OPERATION_LOGGING != OPLOG_FULL */
    size = OP_ENTRY_SIZE(id);

    /* Check for reallocation */
    while (unlikely(*next + size >= tx->op_log.size))
      stm_allocate_ol_entries(tx, 1);
# if CM == CM_MERGE
#  if OPERATION_LOGGING == OPLOG_FULL
  } else if (tx->merge->policy == STM_MERGE_POLICY_REPLAY) {
    /* Replay merge, reuse the next log entry */
    current = &tx->merge->replay.op_current;
    next = &tx->merge->replay.op_log;
    size = OP_ENTRY_SIZE(id);

    /* Abort if out of room in the log */
    if (unlikely(*next + size > tx->merge->replay.op_log_max)) {
      stm_rollback(tx, STM_ABORT_OTHER);
      return 0;
    }
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  } else {
    /* Manual merge, reuse the next log entry, if possible */
    current = &tx->merge->context.current;
    next = &tx->merge->next;
    size = OP_ENTRY_SIZE(id);

#  if OPERATION_LOGGING == OPLOG_FULL
    /* Flatten if the next entry is occupied */
    if (GET_LOG_ENTRY(tx, *next)->status != OP_STATUS_REVERTED)
      return 1;
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
# endif /* CM == CM_MERGE */
  }

  op_entry_t *e = GET_LOG_ENTRY(tx, *next);
  /* Record the new operation and store the JIT merge handler */
  e->id = id;
  e->parent = *current;
# if CM == CM_MERGE
#  ifdef MERGE_JIT
  e->jit = jit;
  tx->op_mergeable_jit = !!jit;
#  endif /* MERGE_JIT */
# endif /* CM == CM_MERGE */
# if OPERATION_LOGGING == OPLOG_FULL
  e->status = OP_STATUS_STARTED;
#  ifdef READ_SET_ORDERED
  e->reads = STM_INVALID_READ;
#  endif /* READ_SET_ORDERED */

#  if OPERATION_LOGGING == OPLOG_FULL
  assert(_tinystm.op_info.ids[id.idx].fi.rtype->type == FFI_TYPE_VOID || _tinystm.op_info.ids[id.idx].fi.rtype->type == FFI_TYPE_STRUCT || _tinystm.op_info.ids[id.idx].fi.rtype->size <= sizeof(stm_union_t));

  /* Parse and copy the arguments */
  for (unsigned i = 0; i < _tinystm.op_info.ids[id.idx].fi.nargs; ++i) {
    switch (_tinystm.op_info.ids[id.idx].fi.arg_types[i]->type) {
      case FFI_TYPE_INT:
      case FFI_TYPE_SINT8:
      case FFI_TYPE_SINT16:
        e->args[i].sint = va_arg(args, int);
      break;
      case FFI_TYPE_FLOAT:
      case FFI_TYPE_DOUBLE:
        e->args[i].dbl = va_arg(args, double);
      break;
      case FFI_TYPE_UINT8:
      case FFI_TYPE_UINT16:
        e->args[i].uint = va_arg(args, unsigned int);
      break;
      case FFI_TYPE_UINT32:
        e->args[i].uint = va_arg(args, uint32_t);
      break;
      case FFI_TYPE_SINT32:
        e->args[i].sint = va_arg(args, int32_t);
      break;
      case FFI_TYPE_UINT64:
        e->args[i].uint = va_arg(args, uint64_t);
      break;
      case FFI_TYPE_SINT64:
        e->args[i].sint = va_arg(args, int64_t);
      break;
      case FFI_TYPE_POINTER:
        e->args[i].ptr = va_arg(args, void *);
      break;
      default:
        assert(_tinystm.op_info.ids[id.idx].fi.arg_types[i]->type != FFI_TYPE_STRUCT);
        return 0;
      break;
    }
  }
#  endif /* OPERATION_LOGGING == OPLOG_FULL */

#  if CM == CM_MERGE
  tx->op_mergeable_delayed = !!_tinystm.op_info.ids[e->id.idx].delayed;
#  endif /* CM == CM_MERGE */
# endif /* OPERATION_LOGGING == OPLOG_FULL */

# if OPERATION_LOGGING == OPLOG_FULL
  current->idx = *next;
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  *next += size;
  return 1;
}

static INLINE int
int_stm_end_op(struct stm_tx *tx, const stm_op_id_t id, const void *ret) {
# ifdef DEBUG_OP_LOG
  PRINT_DEBUG("==> stm_end_op(%p[%lu],0x%lx[%s],r:%p)\n", tx, (unsigned long)tx->end, id.idx, _tinystm.op_info.ids[id.idx].name, ret);
# else
  PRINT_DEBUG("==> stm_end_op(%p[%lu],0x%lx,r:%p)\n", tx, (unsigned long)tx->end, id.idx, ret);
# endif /* DEBUG_OP_LOG */

  int flatten_ok = 0;
  stm_op_t *current;

  assert(IS_ACTIVE(tx->status));

  assert(OPID_VALID(id));
  if (unlikely(!OPID_VALID(id)))
    return 0;

# if CM == CM_MERGE && defined(MERGE_FEEDBACK)
  if (!_tinystm.op_info.ids[id.idx].enabled)
    return 1;
# endif /* CM == CM_MERGE && MERGE_FEEDBACK */

  if (
#  if CM == CM_MERGE
    likely(!tx->merge)
#  else
    1
#  endif /* CM == CM_MERGE */
  ) {
    /* Regular operation, no merging */
    current = &tx->op_current;
# if CM == CM_MERGE
#  if OPERATION_LOGGING == OPLOG_FULL
  } else if (tx->merge->policy == STM_MERGE_POLICY_REPLAY) {
    /* Replay merge */
    current = &tx->merge->replay.op_current;
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
  } else {
    /* Manual merge */
    current = &tx->merge->context.current;

#  if OPERATION_LOGGING == OPLOG_FULL
    /* Flattening */
    flatten_ok = 1;
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
# endif /* CM == CM_MERGE */
  }

  assert(OP_VALID(tx, *current));
  /* Check the current operation is valid */
  if (unlikely(!OP_VALID(tx, *current)))
    return 0;

  op_entry_t *e = GET_LOG_ENTRY(tx, current->idx);
# if OPERATION_LOGGING == OPLOG_FULL
  assert((e->status == OP_STATUS_STARTED && STM_SAME_OPID(id, e->id)) || flatten_ok);
# endif /* OPERATION_LOGGING */
  /* Check the current operation has started and its id matches */
  if (unlikely(!STM_SAME_OPID(id, e->id))
# if OPERATION_LOGGING == OPLOG_FULL
    || unlikely(e->status != OP_STATUS_STARTED)
# endif /* OPERATION_LOGGING == OPLOG_FULL */
    )
    return flatten_ok;

#  if OPERATION_LOGGING == OPLOG_FULL
  assert((_tinystm.op_info.ids[id.idx].fi.rtype->type == FFI_TYPE_VOID && !ret) || (_tinystm.op_info.ids[id.idx].fi.rtype->type != FFI_TYPE_VOID && ret));
  /* Check the return value is consistent */
  if (unlikely(_tinystm.op_info.ids[id.idx].fi.rtype->type == FFI_TYPE_VOID && ret) || (_tinystm.op_info.ids[id.idx].fi.rtype->type != FFI_TYPE_VOID && !ret))
    return 0;

  /* Parse and copy the return value */
  if (_tinystm.op_info.ids[id.idx].fi.rtype->type != FFI_TYPE_VOID) {
    switch (_tinystm.op_info.ids[id.idx].fi.rtype->type) {
      case FFI_TYPE_INT:
      case FFI_TYPE_SINT8:
      case FFI_TYPE_SINT16:
        e->args[_tinystm.op_info.ids[id.idx].fi.nargs].sint = *(int *)ret;
      break;
      case FFI_TYPE_FLOAT:
      case FFI_TYPE_DOUBLE:
        e->args[_tinystm.op_info.ids[id.idx].fi.nargs].dbl = *(double *)ret;
      break;
      case FFI_TYPE_UINT8:
      case FFI_TYPE_UINT16:
        e->args[_tinystm.op_info.ids[id.idx].fi.nargs].uint = *(unsigned int *)ret;
      break;
      case FFI_TYPE_UINT32:
        e->args[_tinystm.op_info.ids[id.idx].fi.nargs].uint = *(uint32_t *)ret;
      break;
      case FFI_TYPE_SINT32:
        e->args[_tinystm.op_info.ids[id.idx].fi.nargs].sint = *(int32_t *)ret;
      break;
      case FFI_TYPE_UINT64:
        e->args[_tinystm.op_info.ids[id.idx].fi.nargs].uint = *(uint64_t *)ret;
      break;
      case FFI_TYPE_SINT64:
        e->args[_tinystm.op_info.ids[id.idx].fi.nargs].sint = *(int64_t *)ret;
      break;
      case FFI_TYPE_STRUCT:
        e->args[_tinystm.op_info.ids[id.idx].fi.nargs].ptr = &e->args[_tinystm.op_info.ids[id.idx].fi.nargs + 1];
        memcpy(&e->args[_tinystm.op_info.ids[id.idx].fi.nargs + 1], ret, _tinystm.op_info.ids[id.idx].fi.rtype->size);
      break;
      case FFI_TYPE_POINTER:
        e->args[_tinystm.op_info.ids[id.idx].fi.nargs].ptr = *(void **)ret;
      break;
      default:
        return 0;
      break;
    }
  }
#  endif /* OPERATION_LOGGING == OPLOG_FULL */

  /* Clear the JIT merge handler and pop the current operation */
#  if OPERATION_LOGGING == OPLOG_FULL
  e->status = OP_STATUS_FINISHED;
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
#  if CM == CM_MERGE && defined(MERGE_JIT)
  e->jit = NULL;
#  endif /* CM == CM_MERGE && MERGE_JIT */
  *current = e->parent;
#  if CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL)
  if (OP_VALID(tx, *current)) {
    e = GET_LOG_ENTRY(tx, current->idx);
    tx->op_mergeable_delayed = !!_tinystm.op_info.ids[e->id.idx].delayed;
#   ifdef MERGE_JIT
    tx->op_mergeable_jit = !!e->jit;
#   endif /* MERGE_JIT */
  } else {
    tx->op_mergeable_delayed = 0;
#   ifdef MERGE_JIT
    tx->op_mergeable_jit = 0;
#   endif /* MERGE_JIT */
  }
#  endif /* CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL) */

  return 1;
}

# if OPERATION_LOGGING == OPLOG_FULL
/* Call 'f' with optional argument 'arg' on each operation log entry in the subtree rooted at operation log entry 'o'. */
static INLINE unsigned int
int_stm_iterate_op(struct stm_tx *tx, const stm_op_t o, const stm_op_id_t arg, unsigned int (* const f)(struct stm_tx *, stm_op_t, stm_op_id_t)) {
# ifdef DEBUG_OP_LOG
  PRINT_DEBUG("==> stm_iterate_op(%p[%lu],0x%lx,0x%lx[%s])\n", tx, (unsigned long)tx->end, o.idx, GET_LOG_ENTRY(tx, o.idx)->id.idx, _tinystm.op_info.ids[GET_LOG_ENTRY(tx, o.idx)->id.idx].name);
# else
  PRINT_DEBUG("==> stm_iterate_op(%p[%lu],0x%lx,0x%lx)\n", tx, (unsigned long)tx->end, o.idx, GET_LOG_ENTRY(tx, o.idx)->id.idx);
# endif /* DEBUG_OP_LOG */
  assert(OP_VALID(tx, o));

  /* Store index of the start position */
  stm_op_t end = o;
  /* Iterate until the current log entry reaches the end of the log, or the parent of the current node precedes the start */
  do {
    const unsigned int ret = f(tx, end, arg);
    if (!ret)
      break;
    end.idx += ret;
  } while (OP_VALID(tx, end) && OP_SUBTREE(o.idx, end));

  return end.idx - o.idx;
}
# endif /* OPERATION_LOGGING == OPLOG_FULL */
#endif /* OPERATION_LOGGING != OPLOG_NONE */

#if CM == CM_MERGE
static INLINE void
int_stm_dedup(struct stm_tx *tx, const stm_read_t rtin) {
# if READ_SET == RW_ARRAY || READ_SET == RW_ADAPTIVE
  if (
#  if READ_SET == RW_ADAPTIVE
    !kh_size(tx->r_set.hash)
#  else
    1
#  endif /* READ_SET == RW_ADAPTIVE */
  ) {
    // FIXME: tx->attr.read_set_ordered
# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
    for (stm_read_t rt = { .idx = READ_RESERVED_IDX + 1 }; READ_VALID(tx, rt); ++rt.idx)
# else
    for (stm_read_t rt = { .idx = 0 }; READ_VALID(tx, rt); ++rt.idx)
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
    {
      r_entry_t *r = POINTER_FROM_READ(tx, rt);
      if (r->lock && !STM_SAME_READ(rtin, rt) && kh_read_equal(rtin, rt))
        int_stm_undo_load(tx, r, 1, 0);
    }
  }
# endif /* READ_SET == RW_ARRAY || READ_SET == RW_ADAPTIVE */
}

static INLINE int int_stm_merge_ok(struct stm_tx *tx) {
# ifdef MERGE_MAX
  return tx->stat_merges_ok < MERGE_MAX;
# endif /* MERGE_MAX */
  return 1;
}

static INLINE void int_stm_resume(struct stm_tx *tx) {
  /* Re-increment the nesting counter */
  if (GET_STATUS(tx->status) == TX_COMMITTING)
    tx->nesting++;

  /* Reset transaction status, since jumping back into user code */
  UPDATE_STATUS_RAW(tx->status, TX_ACTIVE_BIT);

  /* Unlock any locks */
  if (tx->w_set_unique.nb_acquired > 0)
    int_stm_unlock(tx);

#ifndef MERGE_UNLOCK
  /* Unset revalidation flag */
  tx->revalidate = REVALIDATE_NONE;
#endif /* !MERGE_UNLOCK */
}

static INLINE stm_word_t
int_stm_load_update(struct stm_tx *tx, r_entry_t *r) {
  if (tx->merge) {
# if DESIGN == WRITE_BACK_CTL
    return stm_wbctl_read_update(tx, r);
# elif DESIGN == MODULAR
    if (tx->attr.id == WRITE_BACK_CTL)
      return stm_wbctl_read_update(tx, r);
# else
#  error "Only support for WRITE_BACK_CTL is implemented!"
# endif /* DESIGN */
  }

  return 0;
}

static INLINE int
int_stm_store_update(struct stm_tx *tx, w_entry_t *w, const stm_word_t v, const stm_word_t mask) {
  if (tx->merge) {
# if DESIGN == WRITE_BACK_CTL
    stm_wbctl_write_update(tx, w, v, mask);
    return 1;
# elif DESIGN == MODULAR
    if (tx->attr.id == WRITE_BACK_CTL) {
      stm_wbctl_write_update(tx, w, v, mask);
      return 1;
    }
# else
#  error "Only support for WRITE_BACK_CTL is implemented!"
# endif /* DESIGN */
  }

  return 0;
}

# if OPERATION_LOGGING != OPLOG_NONE
static INLINE stm_merge_cb_t
int_stm_get_merge(const struct stm_tx *tx, const op_entry_t *e, stm_merge_policy_t *policy) {
  PRINT_DEBUG("==> stm_get_merge(%p[%lu],0x%p,jit:%p,delayed:%p)\n", tx, (unsigned long)tx->end, m, e->jit, _tinystm.op_info.ids[e->id.idx].delayed);

  assert(e && policy);
  assert(_tinystm.op_info.ids[e->id.idx].policy[0] == STM_MERGE_POLICY_FUNCTION || _tinystm.op_info.ids[e->id.idx].delayed);
  if (
# ifdef MERGE_JIT
    e->status == OP_STATUS_STARTED
# else
    0
# endif /* MERGE_JIT */
    ) {
# ifdef MERGE_JIT
    /* Just-in-time merge, function is still on the stack */
    *policy = _tinystm.op_info.ids[e->id.idx].policy[1];
    return e->jit;
# endif /* MERGE_JIT */
  } else if (
# if OPERATION_LOGGING == OPLOG_FULL
    e->status == OP_STATUS_FINISHED
# else
    1
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  ) {
    /* Delayed merge, function has gone out of scope */
    *policy = _tinystm.op_info.ids[e->id.idx].policy[0];
    return _tinystm.op_info.ids[e->id.idx].delayed;
  }
  *policy = STM_MERGE_POLICY_FUNCTION;
  return NULL;
}
#endif /* OPERATION_LOGGING != OPLOG_NONE */

# ifdef READ_SET_ORDERED
#  if CM == CM_MERGE
static INLINE void
int_stm_load_position(struct stm_tx *tx, merge_context_t *merge, op_entry_t *e) {
  PRINT_DEBUG("==> stm_load_position(%p[%lu],%p,%p)\n", tx, (unsigned long)tx->end, merge, e);

  assert(merge == tx->merge);
  /* Set the position where new reads should be appended */
# if OPERATION_LOGGING == OPLOG_FULL
  if (merge->policy == STM_MERGE_POLICY_FUNCTION) {
# endif /* OPERATION_LOGGING == OPLOG_FULL */
    if (merge->context.leaf) {
      /* Leaf conflict: after the conflicting read */
      assert(ENTRY_VALID(merge->context.conflict.entries->e1));
      assert(GET_LOG_ENTRY(tx, POINTER_FROM_READ(tx, ENTRY_GET_READ(merge->context.conflict.entries->e1))->op.idx)->status != OP_STATUS_REVERTED);
      merge->context.read = ENTRY_GET_READ(merge->context.conflict.entries->e1);
    } else {
      assert(STM_SAME_READ(merge->context.read, STM_INVALID_READ));
      /* Recursive conflict: store lazy placeholder value */
      merge->context.read.idx = STM_SPECIAL_OP.idx;
    }
# if OPERATION_LOGGING == OPLOG_FULL
  } else {
    /* Replay merge: immediately before the current operation */
    assert(merge->policy == STM_MERGE_POLICY_REPLAY);
    merge->context.read = int_stm_load_prev(tx, merge->context.current, e->reads);
  }
# endif /* OPERATION_LOGGING == OPLOG_FULL */
}
#  endif /* CM == CM_MERGE */

static INLINE stm_read_t *
int_stm_get_load_position(struct stm_tx *tx) {
  assert(tx->merge);
  if (tx->merge->context.read.idx == STM_SPECIAL_OP.idx) {
    /* Recursive conflict: force evaluation of lazy placeholder value */
    assert(!tx->merge->context.leaf);
    assert(tx->merge->policy == STM_MERGE_POLICY_FUNCTION);
    const op_entry_t *e = GET_LOG_ENTRY(tx, tx->merge->context.current.idx);
    /* Check if this operation has any reads */
    if (READ_VALID_FAST(tx, e->reads)) {
      /* Recursive conflict: default to after the end of the current operation's reads */
      tx->merge->context.read = int_stm_load_last(tx, e->reads);
    } else {
      /* Recursive conflict: default to after the end of the previous operation's reads */
      tx->merge->context.read = int_stm_load_prev(tx, tx->merge->context.current, STM_INVALID_READ);
    }
  } else if (tx->merge->policy == STM_MERGE_POLICY_FUNCTION && tx->merge->context.leaf) {
    /* User-specified position must be after the conflict */
    assert(tx->attr.read_set_ordered || tx->merge->context.read.idx >= ENTRY_GET_READ(tx->merge->context.conflict.entries->e1).idx);
  }

  assert(!READ_VALID(tx, tx->merge->context.read) || (POINTER_FROM_READ(tx, tx->merge->context.read)->lock && (!OP_VALID(tx, POINTER_FROM_READ(tx, tx->merge->context.read)->next) || !STM_SAME_OP(POINTER_FROM_READ(tx, POINTER_FROM_READ(tx, tx->merge->context.read)->next)->op, tx->merge->context.current) || STM_SAME_OP(POINTER_FROM_READ(tx, tx->merge->context.read)->op, tx->merge->context.current)))
  );
  return &tx->merge->context.read;
}
# endif /* READ_SET_ORDERED */

# if OPERATION_LOGGING == OPLOG_FULL
static INLINE void
int_stm_op_update(struct stm_tx *tx, merge_context_t *merge, unsigned char *dst, const unsigned int sz) {
  PRINT_DEBUG("==> stm_op_update(%p[%lu],%p,%lx)\n", tx, (unsigned long)tx->end, dst, sz);

  /* Flush any pending update to the operation log */
  if (merge->update.size) {
    PRINT_DEBUG("==> writing rv(new):0x%lx dst:%p sz:0x%lx\n", merge->update.src.uint, merge->update.dst, merge->update.size);

    if (merge->update.size == 1) {
      assert(merge->update.dst + sz < tx->op_log.entries + tx->op_log.used);
      *(stm_union_t *)merge->update.dst = merge->update.src;
    } else {
      memcpy(merge->update.dst, merge->update.src.ptr, merge->update.size);
      free(merge->update.src.ptr);
    }

    merge->update.size = 0;
  }

  /* Queue the new update */
  if (sz) {
# ifdef DEBUG_OP_LOG
    PRINT_DEBUG("==> queuing rv(new):0x%lx dst:0x%lx sz:0x%lx\n", src->uint, dst, sz);
# endif /* DEBUG_OP_LOG */
    merge->update.src = merge->context.rv;
    assert(sz == 1 ? dst < tx->op_log.entries + tx->op_log.used : 1);
    merge->update.dst = dst;
    assert(sz < tx->op_log.used);
    merge->update.size = sz;
    assert(sz == 1 ? dst + sz < tx->op_log.entries + tx->op_log.used : 1);
  }
}
# endif /* OPERATION_LOGGING == OPLOG_FULL */

static INLINE void
int_stm_undo_store(struct stm_tx *tx, w_entry_t *w) {
  PRINT_DEBUG("==> stm_undo_store(%p[%lu],%p)\n", tx, (unsigned long)tx->end, w);

  assert(tx->w_set.nb_entries > 0 && tx->w_set_unique.nb_entries);
  assert(WRITE_POINTER_VALID(tx, w) && WRITE_UNIQUE_VALID(tx, w->unique));
# if OPERATION_LOGGING == OPLOG_FULL
  assert(OP_VALID(tx, w->op));
# endif /* OPERATION_LOGGING == OPLOG_FULL */

# ifdef DEBUG_OP_LOG
  stm_version_t l = LOCK_READ(w->lock);
  assert(!LOCK_GET_OWNED(w->addr, l) || (LOCK_GET_OWNED(w->addr, l) && (w != (w_entry_t *)LOCK_GET_ADDR(l))));
# endif /* DEBUG_OP_LOG */

# if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
  if (
#  if WRITE_SET == RW_ADAPTIVE
    kh_size(tx->w_set.hash)
#  else
    1
#  endif /* WRITE_SET == RW_ADAPTIVE */
  ) {
    const stm_write_t wt = WRITE_FROM_POINTER(tx, w);
    khiter_t it = kh_get(w_set, tx->w_set.hash, wt);
    assert(it != kh_end(tx->w_set.hash));
    /* Update the latest write to this address in the current operation */
    if (STM_SAME_WRITE(kh_key(tx->w_set.hash, it), wt)) {
      /* This is the latest write, so delete it */
      kh_del(w_set, tx->w_set.hash, it);

#  if OPERATION_LOGGING == OPLOG_FULL
      /* Check if an earlier write exists */
      if (WRITE_VALID_FAST(tx, w->addr_prev)) {
        stm_write_t prev = int_stm_store_prev(tx, w->addr_prev, w->op);
        if (WRITE_VALID_FAST(tx, prev)) {
          assert(STM_SAME_OP(w->op, POINTER_FROM_WRITE(tx, prev)->op) && !STM_SAME_WRITE(prev, wt));
          int ret;
          /* Set it as the new latest write */
          kh_put(w_set, tx->w_set.hash, prev, &ret);
          assert(ret >= 0);
        }
      }
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
    }
  }
# endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */

# if OPERATION_LOGGING == OPLOG_FULL
  /* Remove this entry from the list of all writes to this address */
  const stm_write_t next = int_stm_store_next(tx, w);
  assert(WRITE_VALID(tx, next) == !STM_SAME_WRITE(POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->latest, WRITE_FROM_POINTER(tx, w)));
  if (WRITE_VALID_FAST(tx, next)) {
    /* Update the next write to skip this entry */
    w_entry_t *next_w = POINTER_FROM_WRITE(tx, next);
    next_w->addr_prev = w->addr_prev;
  } else
    POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->latest = w->addr_prev;
# elif OPERATION_LOGGING != OPLOG_NONE
  POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->latest = STM_INVALID_WRITE;
# endif /* OPERATION_LOGGING */

# if !defined(NDEBUG) && defined(READ_SET_SOURCE) && (OPERATION_LOGGING == OPLOG_FULL)
  if (tx->merge && tx->merge->context.leaf) {
    r_entry_t *r;
    for (stm_read_t rt = GET_LOG_ENTRY(tx, tx->merge->context.current.idx)->reads; READ_VALID(tx, rt) && !STM_SAME_READ(rt, ENTRY_GET_READ(tx->merge->context.conflict.entries->e1));
        rt =
# ifdef READ_SET_ORDERED
        tx->attr.read_set_ordered ? r->next :
# endif /* READ_SET_ORDERED */
        READ_FROM_POINTER(tx, r + 1)
    ) {
      r = POINTER_FROM_READ(tx, rt);
      assert(!STM_SAME_WRITE(r->source, WRITE_FROM_POINTER(tx, w)));
    }
  }

#endif /* !NDEBUG && READ_SET_SOURCE && (OPERATION_LOGGING == OPLOG_FULL) */

# if defined(READ_SET_SOURCE) && (DETECTION == TIME_BASED)
  ++w->version;
# endif /* READ_SET_SOURCE && (DETECTION == TIME_BASED) */
  w->mask = 0;
# if OPERATION_LOGGING == OPLOG_FULL
  w->op = STM_SPECIAL_OP;
# endif /* OPERATION_LOGGING == OPLOG_FULL */

# ifdef TM_STATISTICS
  ++tx->stat_reverted_writes;
# endif /* TM_STATISTICS */
}

# if OPERATION_LOGGING == OPLOG_FULL
static INLINE void
int_stm_clear_write(struct stm_tx *tx, const stm_op_t o) {
  /* Search and remove matching entries from the write set */
# if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE || WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
for (w_entry_t *w = tx->w_set.entries + WRITE_RESERVED_IDX + 1; w < tx->w_set.entries + tx->w_set.nb_entries; ++w)
# else
for (w_entry_t *w = tx->w_set.entries; w < tx->w_set.entries + tx->w_set.nb_entries; ++w)
# endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE || WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
  {
    if (STM_SAME_OP(w->op, o))
      int_stm_undo_store(tx, w);
  }
}

static INLINE void
int_stm_clear_read(struct stm_tx *tx, const stm_op_t o, op_entry_t *e) {
  r_entry_t *r;
  const unsigned int ordered = tx->attr.read_set_ordered;
  assert(e->status != OP_STATUS_REVERTED);

  /* Search and remove matching entries from the read set */
  if (!READ_VALID_FAST(tx, e->reads))
    return;

# ifdef READ_SET_ORDERED
  if (ordered) {
    /* Get the predecessor of the first entry */
    stm_read_t prev = int_stm_load_prev(tx, o, e->reads);
    assert(!STM_SAME_OP(prev, e->reads));
    assert(!READ_VALID(tx, prev) || STM_SAME_READ(POINTER_FROM_READ(tx, prev)->next, e->reads));

    /* Update other potential references to this operation's reads */
    if (tx->merge && READ_VALID_FAST(tx, tx->merge->context.read) && STM_SAME_OP(o, POINTER_FROM_READ(tx, tx->merge->context.read)->op))
      tx->merge->context.read = prev;
    if (READ_VALID_FAST(tx, tx->r_set.tail) && STM_SAME_OP(o, POINTER_FROM_READ(tx, tx->r_set.tail)->op))
      tx->r_set.tail = prev;

    /* Remove all the entries directly, without updating each incrementally */
    stm_read_t head = e->reads, tail = STM_INVALID_READ, tail_next = STM_INVALID_READ, current = e->reads;
    /* (prev -> [head -> ... -> tail] -> ... -> (prev -> [head -> ... -> tail]) -> tail_next -> ... */
    while (1) {
      if (!READ_VALID_FAST(tx, current)) {
        r = NULL;
        goto update;
      }

      r = POINTER_FROM_READ(tx, current);
      assert(r->lock);

      if (STM_SAME_OP(o, r->op)) {
        if (!READ_VALID_FAST(tx, head))
          head = current;
        tail = current;

        assert(STM_SAME_OP(o, r->op));
        int_stm_undo_load(tx, r, 0, 0);
        assert(STM_SAME_OP(current, e->reads) || !STM_SAME_OP(current, tx->r_set.head));
      } else {
update:
        if (READ_VALID_FAST(tx, tail)) {
          assert(READ_VALID(tx, head));

          /* Store the read after the tail, because it is overwritten when the sublist is added to the free list */
          tail_next = POINTER_FROM_READ(tx, tail)->next;

          /* Update the predecessor to skip over this sublist */
          if (READ_VALID_FAST(tx, prev)) {
            assert(STM_SAME_READ(POINTER_FROM_READ(tx, prev)->next, head));
            POINTER_FROM_READ(tx, prev)->next = tail_next;
          }

          /* Insert this sublist onto the free list of read set entries */
          POINTER_FROM_READ(tx, tail)->next = tx->r_set.free;
          tx->r_set.free = head;

          prev = STM_INVALID_READ;
          head = STM_INVALID_READ;
          tail = STM_INVALID_READ;
        }

        if (!r || (OP_VALID(tx, r->op) && !OP_SUBTREE(o.idx, r->op)))
          break;

        prev = current;
      }

      assert(!STM_SAME_READ(current, r->next));
      current = r->next;
    }

    /* Update other potential references to this operation's reads */
    if (STM_SAME_READ(tx->r_set.head, e->reads))
      tx->r_set.head = tail_next;

    e->reads = STM_INVALID_READ;
  } else {
# endif /* READ_SET_ORDERED */
    e->reads = STM_INVALID_READ;

    for (stm_read_t rt = { .idx =
# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
      READ_RESERVED_IDX + 1
# else
      0
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
      }; likely(READ_VALID_FAST(tx, rt));
# ifdef READ_SET_ORDERED
      rt = (ordered ? r->next :
# endif /* READ_SET_ORDERED */
      READ_FROM_POINTER(tx, r + 1))
    ) {
      r = POINTER_FROM_READ(tx, rt);
# if defined(READ_SET_ORDERED)
      if (tx->attr.read_set_ordered)
        assert(r->lock);
      else if (!r->lock)
        continue;
# else
      if (!r->lock)
        continue;
# endif /* READ_SET_ORDERED */

      if (STM_SAME_OP(r->op, o))
        int_stm_undo_load(tx, r, 1, 0);
    }
# ifdef READ_SET_ORDERED
  }
# endif /* READ_SET_ORDERED */
}

static unsigned int
int_stm_undo_op(struct stm_tx *tx, const stm_op_t o, const stm_op_id_t arg) {
# ifdef DEBUG_OP_LOG
  PRINT_DEBUG("==> stm_undo_op(%p[%lu],0x%lx,0x%lx[%s])\n", tx, (unsigned long)tx->end, o.idx, GET_LOG_ENTRY(tx, o.idx)->id.idx, _tinystm.op_info.ids[GET_LOG_ENTRY(tx, o.idx)->id.idx].name);
# else
  PRINT_DEBUG("==> stm_undo_op(%p[%lu],0x%lx,0x%lx)\n", tx, (unsigned long)tx->end, o.idx, GET_LOG_ENTRY(tx, o.idx)->id.idx);
# endif /* DEBUG_OP_LOG */

  assert(OP_VALID(tx, o));
  op_entry_t *e = GET_LOG_ENTRY(tx, o.idx);
  assert(OPID_VALID(e->id));
  const unsigned int sz = OP_ENTRY_SIZE(e->id);

  /* Check if it has been cleared already */
  if (e->status == OP_STATUS_REVERTED)
    return sz;

  /* Clear any stores */
  int_stm_clear_write(tx, o);

  /* Clear any loads */
  int_stm_clear_read(tx, o, e);

  /* Undo any dynamic memory operations */
  stm_undo_mem_op(o);

  /* Clear the JIT merge handler and mark invalid */
#ifdef MERGE_JIT
  e->jit = NULL;
  tx->op_mergeable_jit = 0;
#endif /* MERGE_JIT */
  e->status = OP_STATUS_REVERTED;

  /* Ensure the current operation is valid */
  while (OP_VALID(tx, tx->op_current)) {
    e = GET_LOG_ENTRY(tx, tx->op_current.idx);
    if (e->status != OP_STATUS_REVERTED)
      break;
    tx->op_current = e->parent;
  }

# ifdef TM_STATISTICS
  tx->stat_reverted_ops += sz;
# endif /* TM_STATISTICS */

  return sz;
}

static unsigned int
int_stm_undo_op_descendants(struct stm_tx *tx, const stm_op_t o, const stm_op_id_t arg) {
# ifdef DEBUG_OP_LOG
  PRINT_DEBUG("==> stm_undo_op_descendants(%p[%lu],0x%lx,0x%lx,0x%lx[%s])\n", tx, (unsigned long)tx->end, arg.idx, o.idx, GET_LOG_ENTRY(tx, o.idx)->id.idx, _tinystm.op_info.ids[GET_LOG_ENTRY(tx, o.idx)->id.idx].name);
# else
  PRINT_DEBUG("==> stm_undo_op_descendants(%p[%lu],0x%lx,0x%lx,0x%lx)\n", tx, (unsigned long)tx->end, arg.idx, o.idx, GET_LOG_ENTRY(tx, o.idx)->id.idx);
# endif /* DEBUG_OP_LOG */

  assert(OP_VALID(tx, o));
  assert(OPID_VALID(arg));
  const op_entry_t *e = GET_LOG_ENTRY(tx, o.idx);
  assert(OPID_VALID(e->id));
  if (STM_SAME_OPID(e->id, arg))
    return int_stm_iterate_op(tx, o, arg, int_stm_undo_op);
  return OP_ENTRY_SIZE(e->id);
}

static unsigned int
int_stm_find_op_descendant(struct stm_tx *tx, const stm_op_t o, const stm_op_id_t arg) {
# ifdef DEBUG_OP_LOG
  PRINT_DEBUG("==> stm_find_op_descendants(%p[%lu],0x%lx,0x%lx,0x%lx[%s])\n", tx, (unsigned long)tx->end, arg.idx, o.idx, GET_LOG_ENTRY(tx, o.idx)->id.idx, _tinystm.op_info.ids[GET_LOG_ENTRY(tx, o.idx)->id.idx].name);
# else
  PRINT_DEBUG("==> stm_find_op_descendants(%p[%lu],0x%lx,0x%lx,0x%lx)\n", tx, (unsigned long)tx->end, arg.idx, o.idx, GET_LOG_ENTRY(tx, o.idx)->id.idx);
# endif /* DEBUG_OP_LOG */

  assert(OP_VALID(tx, o));
  assert(OPID_VALID(arg));
  const op_entry_t *e = GET_LOG_ENTRY(tx, o.idx);
  assert(OPID_VALID(e->id));
  if (STM_SAME_OPID(e->id, arg))
    return 0;
  return OP_ENTRY_SIZE(e->id);
}
# endif /* OPERATION_LOGGING == OPLOG_FULL */
#endif /* CM == CM_MERGE */

static void
int_stm_undo_load(struct stm_tx *tx, r_entry_t *r, const int unlink
#if CM == CM_MERGE
  , const int dedup
#endif /* CM == CM_MERGE */
  ) {
# ifdef READ_SET_ORDERED
  const unsigned int ordered = tx->attr.read_set_ordered;
# endif /* READ_SET_ORDERED */

  PRINT_DEBUG("==> stm_undo_load(%p[%lu],%p,%d)\n", tx, (unsigned long)tx->end, r->addr, unlink);

  assert(tx->r_set.nb_entries > 0);
  assert(READ_POINTER_VALID(tx, r));

# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE || defined(READ_SET_ORDERED)
  const stm_read_t rt = READ_FROM_POINTER(tx, r);
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE || READ_SET_ORDERED */

# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
  if (kh_size(tx->r_set.hash)) {
    /* Remove this read from the hash table */
    khiter_t it = kh_get(r_set, tx->r_set.hash, rt);
    if (it != kh_end(tx->r_set.hash) && STM_SAME_READ(kh_key(tx->r_set.hash, it), rt))
      kh_del(r_set, tx->r_set.hash, it);
  }
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */

# if CM == CM_MERGE
  /* Perform deduplication now */
  if (dedup)
    int_stm_dedup(tx, rt);
# endif /* CM = CM_MERGE */

# ifdef READ_SET_ORDERED
  /* Remove this entry */
  if (unlink) {
    stm_read_t prev_rt;

    /* Find the predecessor */
    if (ordered || (tx->merge && STM_SAME_READ(rt, tx->merge->context.read))) {
      prev_rt = int_stm_load_prev(tx,
# if OPERATION_LOGGING != OPLOG_NONE
        r->op,
# endif /* OPERATION_LOGGING != OPLOG_NONE */
        rt);
      assert(!ordered || !READ_VALID(tx, prev_rt) || STM_SAME_READ(POINTER_FROM_READ(tx, prev_rt)->next, rt));
    }

    /* Update other potential references to this read */
    if (tx->merge && STM_SAME_READ(rt, tx->merge->context.read))
      tx->merge->context.read = prev_rt;

# if OPERATION_LOGGING == OPLOG_FULL
    if (OP_VALID(tx, r->op)) {
      op_entry_t *e = GET_LOG_ENTRY(tx, r->op.idx);
      assert(!(ordered || (tx->merge && STM_SAME_READ(rt, tx->merge->context.read))) || !STM_SAME_OP(prev_rt, e->reads));
      if (e && STM_SAME_READ(rt, e->reads))
        e->reads = int_stm_load_next(tx, rt, 1, 0);
    }
# endif /* OPERATION_LOGGING == OPLOG_FULL */

    if (ordered) {
      /* Update the previous read to skip this entry */
      if (READ_VALID_FAST(tx, prev_rt)) {
        r_entry_t *pred_r = POINTER_FROM_READ(tx, prev_rt);
        pred_r->next = r->next;
      }

      if (STM_SAME_READ(rt, tx->r_set.head))
        tx->r_set.head = r->next;
      if (STM_SAME_READ(rt, tx->r_set.tail))
        tx->r_set.tail = prev_rt;

      /* Insert this entry into the free list of read set entries */
      r->next = tx->r_set.free;
      tx->r_set.free = rt;
    }
  }
# endif /* READ_SET_ORDERED */

# if DETECTION == TIME_BASED
  assert(r->lock);
  /* Set this entry to a tombstone value */
  r->lock = NULL;
# endif /* DETECTION == TIME_BASED */

# if CM == CM_MERGE && defined(TM_STATISTICS)
  ++tx->stat_reverted_reads;
# endif /* CM == CM_MERGE && TM_STATISTICS */
}

#endif /* _STM_INTERNAL_H_ */
