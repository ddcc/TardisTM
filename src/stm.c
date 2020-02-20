/*
 * File:
 *   stm.c
 * Author(s):
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * Description:
 *   STM functions.
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
#include <signal.h>
#include <stdio.h>
#include <string.h>

#include <pthread.h>
#include <sched.h>

#include "stm.h"
#include "stm_internal.h"
#include "mod_stats.h"

#include "utils.h"
#include "atomic.h"
#include "gc.h"

/* ################################################################### *
 * DEFINES
 * ################################################################### */

/* Indexes are defined in stm_internal.h  */
static const char *design_names[] = {
  /* 0 */ "WRITE-BACK (ETL)",
  /* 1 */ "WRITE_BACK (ETL, VR)",
  /* 2 */ "WRITE-BACK (CTL)",
  /* 3 */ "WRITE-THROUGH",
  /* 4 */ "WRITE-MODULAR"
};

static const char *cm_names[] = {
  /* 0 */ "RESTART",
  /* 1 */ "AGGRESSIVE",
  /* 2 */ "DELAY",
  /* 3 */ "TIMESTAMP",
  /* 4 */ "BACKOFF",
  /* 5 */ "KARMA",
  /* 6 */ "MERGE"
};

/* Global variables */
global_t _tinystm =
    {
#if OPERATION_LOGGING != OPLOG_NONE
      .op_info.ids = NULL,
#endif /* OPERATION_LOGGING != OPLOG_NONE */
      .nb_specific = 0,
      .initialized = 0,
#ifdef IRREVOCABLE_ENABLED
      .irrevocable = 0,
#endif /* IRREVOCABLE_ENABLED */
    };

/* ################################################################### *
 * TYPES
 * ################################################################### */


/*
 * Transaction nesting is supported in a minimalist way (flat nesting):
 * - When a transaction is started in the context of another
 *   transaction, we simply increment a nesting counter but do not
 *   actually start a new transaction.
 * - The environment to be used for setjmp/longjmp is only returned when
 *   no transaction is active so that it is not overwritten by nested
 *   transactions. This allows for composability as the caller does not
 *   need to know whether it executes inside another transaction.
 * - The commit of a nested transaction simply decrements the nesting
 *   counter. Only the commit of the top-level transaction will actually
 *   carry through updates to shared memory.
 * - An abort of a nested transaction will rollback the top-level
 *   transaction and reset the nesting counter. The call to longjmp will
 *   restart execution before the top-level transaction.
 * Using nested transactions without setjmp/longjmp is not recommended
 * as one would need to explicitly jump back outside of the top-level
 * transaction upon abort of a nested transaction. This breaks
 * composability.
 */

/*
 * Reading from the previous version of locked addresses is implemented
 * by peeking into the write set of the transaction that owns the
 * lock. Each transaction has a unique identifier, updated even upon
 * retry. A special "commit" bit of this identifier is set upon commit,
 * right before writing the values from the redo log to shared memory. A
 * transaction can read a locked address if the identifier of the owner
 * does not change between before and after reading the value and
 * version, and it does not have the commit bit set.
 */

/* ################################################################### *
 * THREAD-LOCAL
 * ################################################################### */

#if defined(TLS_POSIX) || defined(TLS_DARWIN)
/* TODO this may lead to false sharing. */
/* TODO this could be renamed with tinystm prefix */
pthread_key_t thread_tx;
pthread_key_t thread_gc;
#elif defined(TLS_COMPILER)
__thread stm_tx_t* thread_tx = NULL;
__thread long thread_gc = 0;
#endif /* defined(TLS_COMPILER) */

/* ################################################################### *
 * STATIC
 * ################################################################### */

#if CM == CM_MERGE
static INLINE int
int_stm_merge_finish(struct stm_tx *tx, merge_context_t *merge
# if OPERATION_LOGGING != OPLOG_NONE
  , op_entry_t *e
# endif /* OPERATION_LOGGING != OPLOG_NONE */
  ) {
  int recurse = 0;

  /* End the merge */
  assert(merge && tx->merge == merge);
  tx->merge = NULL;
# if OPERATION_LOGGING == OPLOG_FULL
  tx->op_mergeable_delayed = !!_tinystm.op_info.ids[e->id.idx].delayed;
#  ifdef MERGE_JIT
  tx->op_mergeable_jit = !!e->jit;
#  endif /* MERGE_JIT */
# endif /* OPERATION_LOGGING == OPLOG_FULL */

  switch (merge->result) {
    case STM_MERGE_OK:
    case STM_MERGE_OK_PARENT:
    case STM_MERGE_OK_USER:
# ifdef MERGE_FEEDBACK
      tx->feedback[e->id.idx] = 1;
      ATOMIC_FETCH_INC_FULL(&_tinystm.op_info.ids[e->id.idx].repairs_ok);
# endif /* MERGE_FEEDBACK */
# ifdef TM_STATISTICS
#  ifdef TM_STATISTICS2
      if (!tx->stat_merges_ok)
        tx->stat_work_merge = get_time();
#  endif /* TM_STATISTICS2 */
      ++tx->stat_merges_ok;
# endif /* TM_STATISTICS */
      break;
    case STM_MERGE_RETRY:
# ifdef TM_STATISTICS
      ++tx->stat_merges_retry;
# endif /* TM_STATISTICS */
      break;
    default:
      break;
  }

  /* Determine whether to recurse */
  if (merge->result == STM_MERGE_OK) {
    /* Inspect the return value */
    const stm_union_t *rv = &e->args[_tinystm.op_info.ids[e->id.idx].fi.nargs];

    switch (_tinystm.op_info.ids[e->id.idx].fi.rtype->type) {
      case FFI_TYPE_INT:
      case FFI_TYPE_SINT8:
      case FFI_TYPE_SINT16:
        recurse = merge->context.rv.sint != rv->sint;
      break;
      case FFI_TYPE_FLOAT:
      case FFI_TYPE_DOUBLE:
        recurse = merge->context.rv.dbl != rv->dbl;
      break;
      case FFI_TYPE_UINT8:
      case FFI_TYPE_UINT16:
        recurse = merge->context.rv.uint != rv->uint;
      break;
      case FFI_TYPE_UINT32:
        recurse = (uint32_t)merge->context.rv.uint != (uint32_t)rv->uint;
      break;
      case FFI_TYPE_SINT32:
        recurse = (int32_t)merge->context.rv.sint != (int32_t)rv->sint;
      break;
      case FFI_TYPE_UINT64:
        recurse = (uint64_t)merge->context.rv.uint != (uint64_t)rv->uint;
      break;
      case FFI_TYPE_SINT64:
        recurse = (int64_t)merge->context.rv.sint != (uint64_t)rv->sint;
      break;
      case FFI_TYPE_STRUCT:
# if OPERATION_LOGGING == OPLOG_FULL
        assert(merge->context.rv.ptr && rv->ptr);
        recurse = memcmp(merge->context.rv.ptr, rv->ptr, _tinystm.op_info.ids[e->id.idx].fi.rtype->size);
# endif /* OPERATION_LOGGING */
      break;
      case FFI_TYPE_POINTER:
        recurse = merge->context.rv.ptr != rv->ptr;
      break;
      default:
        merge->result = STM_MERGE_ABORT;
        /* fall through */
      case FFI_TYPE_VOID:
        recurse = 0;
      break;
    }
  } else if (merge->result == STM_MERGE_OK_PARENT) {
    recurse = 1;
  } else {
    recurse = 0;
  }

  /* No parent available */
  if (recurse && !OP_VALID(tx, e->parent)) {
    merge->result = STM_MERGE_UNSUPPORTED;
    recurse = 0;
  }

# if OPERATION_LOGGING == OPLOG_FULL
  /* Handle the return value */
  switch (_tinystm.op_info.ids[e->id.idx].fi.rtype->type) {
    case FFI_TYPE_VOID:
    break;
    case FFI_TYPE_STRUCT:
      /* Queue update if successful, otherwise free the allocation */
      if (merge->result == STM_MERGE_OK || merge->result == STM_MERGE_OK_PARENT) {
        assert(_tinystm.op_info.ids[e->id.idx].fi.rtype->size != 1);
        int_stm_op_update(tx, merge, e->args[_tinystm.op_info.ids[e->id.idx].fi.nargs].ptr, _tinystm.op_info.ids[e->id.idx].fi.rtype->size);
      } else
        free(merge->context.rv.ptr);
    break;
    default:
      /* Queue update if successful */
      if (merge->result == STM_MERGE_OK || merge->result == STM_MERGE_OK_PARENT)
        int_stm_op_update(tx, merge, (unsigned char *)&e->args[_tinystm.op_info.ids[e->id.idx].fi.nargs], 1);
    break;
  }

  /* Force flush of queued update if done */
  if (!recurse)
    int_stm_op_update(tx, merge, 0, 0);
# endif /* OPERATION_LOGGING == OPLOG_FULL */

  return recurse;
}

stm_merge_t stm_merge(struct stm_tx *tx, const stm_conflict_t *c) {
  assert(ENTRY_VALID(c->e1) && ENTRY_GET_READ(c->e1).idx < tx->r_set.size);
  const r_entry_t *r = POINTER_FROM_READ(tx, ENTRY_GET_READ(c->e1));

  /* No log available */
#if OPERATION_LOGGING != OPLOG_NONE
  assert(OP_VALID(tx, r->op));
#endif /* OPERATION_LOGGING != OPLOG_NONE*/

  /* Recursive merge not supported */
  if (tx->merge) {
#if OPERATION_LOGGING == OPLOG_FULL
    /* Replay merge: Conflict is in the same operation that is being replayed, so restart it */
    if (tx->merge->policy == STM_MERGE_POLICY_REPLAY && tx->merge->replay.op_original.idx <= r->op.idx && r->op.idx < tx->merge->replay.op_log_max)
      LONGJMP(tx->merge->replay.env, 1);
#endif /* OPERATION_LOGGING == OPLOG_FULL */
    return STM_MERGE_UNSUPPORTED;
  }

  /* Initialize merge metadata */
  merge_context_t merge = {
    /* Prepare for regular merge or rollback */
# if OPERATION_LOGGING == OPLOG_FULL
    .context.current.idx = r->op.idx,
# endif /* OPERATION_LOGGING */
    .context.previous = STM_INVALID_OP,
    .context.addr = r->addr,
    .context.leaf = 1,
    .context.conflict.entries = c,
    .context.conflict.previous_result.ptr = NULL,
# if OPERATION_LOGGING == OPLOG_FULL
    .context.conflict.result.uint = 0,
# endif /* OPERATION_LOGGING */
    .context.read = STM_INVALID_READ,
    .next = r->op.idx + OP_ENTRY_SIZE(GET_LOG_ENTRY(tx, r->op.idx)->id),
#if OPERATION_LOGGING == OPLOG_FULL
    .replay.op_log_max = 0,
    .update.size = 0,
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  };

  while (1) {
    op_entry_t *e = GET_LOG_ENTRY(tx, merge.context.current.idx);
    assert(OPID_VALID(e->id));

    /* Get the merge function and policy */
    stm_merge_cb_t merge_cb = int_stm_get_merge(tx, e, &merge.policy);
#  ifdef DEBUG_OP_LOG
    printf("==> lookup %lu[%s] = %s\n", merge.context.current.idx, _tinystm.op_info.ids[e->id.idx].name, !merge_cb ? "UNSUPPORTED" : e->status == OP_STATUS_STARTED ? "JIT" : "DELAYED");
#  endif /* DEBUG_OP_LOG */

    if (!merge_cb)
      return STM_MERGE_UNSUPPORTED;

    /* Start a merge in the context of this operation. Will prefer read set deduplication (stale reads) for this operation rather than the current executing operation; see e.g. stm_wbctl_read() */
    assert(!tx->merge || !c);
    tx->merge = &merge;
# if OPERATION_LOGGING == OPLOG_FULL
    tx->op_mergeable_delayed = !!_tinystm.op_info.ids[e->id.idx].delayed;
#  ifdef MERGE_JIT
    tx->op_mergeable_jit = !!e->jit;
#  endif /* MERGE_JIT */
# endif /* OPERATION_LOGGING == OPLOG_FULL */

# ifdef MERGE_FEEDBACK
    ATOMIC_FETCH_INC_FULL(&_tinystm.op_info.ids[e->id.idx].repairs_attempted);
# endif /* MERGE_FEEDBACK */

    if (merge.policy == STM_MERGE_POLICY_REPLAY) {
# if OPERATION_LOGGING == OPLOG_FULL
      /* Set the position for new reads to be appended */
      int_stm_load_position(tx, &merge, e);

      /* Set up the arguments for the replay */
      void *args[_tinystm.op_info.ids[e->id.idx].fi.nargs];
      for (unsigned int i = 0; i < _tinystm.op_info.ids[e->id.idx].fi.nargs; ++i)
        args[i] = &e->args[i];

      /* Set up the return value for the replay */
      if (_tinystm.op_info.ids[e->id.idx].fi.rtype->type == FFI_TYPE_STRUCT)
        merge.context.rv.ptr = malloc(_tinystm.op_info.ids[e->id.idx].fi.rtype->size);

      /* Set the context to handle a conflict inside the replay */
      sigsetjmp(merge.replay.env, 0);

#  ifdef TM_STATISTICS
      ++tx->stat_merges_replay;
#  endif /* TM_STATISTICS */

      /* Revert subtree of this operation and set subtree limit */
      merge.replay.op_original = merge.context.current;
      merge.replay.op_current = e->parent;
      merge.replay.op_log = merge.context.current.idx;
      merge.replay.op_log_max = int_stm_iterate_op(tx, merge.context.current, STM_INVALID_OPID, int_stm_undo_op);
      if (unlikely(merge.replay.op_log_max == STM_BAD_IDX)) {
        assert(tx->merge);
        tx->merge = NULL;
        return STM_MERGE_ABORT;
      }
      merge.replay.op_log_max += merge.replay.op_log;

#  ifdef DEBUG_OP_LOG
      printf("==> ffi_call(%lx[%s])\n", e->id.idx, _tinystm.op_info.ids[e->id.idx].name);
#  endif /* DEBUG_OP_LOG */
      /* Replay the operation */
      ffi_call(&_tinystm.op_info.ids[e->id.idx].fi, _tinystm.op_info.ids[e->id.idx].f, _tinystm.op_info.ids[e->id.idx].fi.rtype->type == FFI_TYPE_STRUCT ? merge.context.rv.ptr : &merge.context.rv, args);

      /* Check proper nesting */
      assert(STM_SAME_OP(merge.replay.op_current, e->parent));
      if (unlikely(!STM_SAME_OP(merge.replay.op_current, e->parent))) {
        if (_tinystm.op_info.ids[e->id.idx].fi.rtype->type == FFI_TYPE_STRUCT)
          free(merge.context.rv.ptr);
        assert(tx->merge);
        tx->merge = NULL;
        return STM_MERGE_ABORT;
      }

      /* Call the merge callback with the new result */
# else
      return STM_MERGE_UNSUPPORTED;
# endif /* OPERATION_LOGGING == OPLOG_FULL */
    } else if (merge.policy == STM_MERGE_POLICY_FUNCTION) {
# ifdef READ_SET_ORDERED
      /* Set the position for new reads to be appended */
      int_stm_load_position(tx, &merge, e);
# endif /* READ_SET_ORDERED */

# if OPERATION_LOGGING == OPLOG_FULL
      /* Copy and initialize the return value */
      if (_tinystm.op_info.ids[e->id.idx].fi.rtype->type == FFI_TYPE_STRUCT) {
        merge.context.rv.ptr = malloc(_tinystm.op_info.ids[e->id.idx].fi.rtype->size);
        memcpy(merge.context.rv.ptr, e->args[_tinystm.op_info.ids[e->id.idx].fi.nargs].ptr, _tinystm.op_info.ids[e->id.idx].fi.rtype->size);
      } else if (_tinystm.op_info.ids[e->id.idx].fi.rtype->type != FFI_TYPE_VOID)
        merge.context.rv = e->args[_tinystm.op_info.ids[e->id.idx].fi.nargs];
# endif /* OPERATION_LOGGING == OPLOG_FULL */

# ifdef TM_STATISTICS
      ++tx->stat_merges_manual;
# endif /* TM_STATISTICS */
      /* Perform the actual merge */
    }

    merge.result = merge_cb(&merge.context);
# ifdef DEBUG_OP_LOG
    printf("==> merge %lu[%s] (%p, %d) = %s\n", merge.context.current.idx, _tinystm.op_info.ids[e->id.idx].name, &merge.context, 0, merge.result == STM_MERGE_OK ? "OK" : merge.result == STM_MERGE_OK_PARENT ? "OK_PARENT" : merge.result == STM_MERGE_ABORT ? "ABORT" : merge.result == STM_MERGE_UNSUPPORTED ? "UNSUPPORTED" : "RETRY");
# endif /* DEBUG_OP_LOG */

    if (!int_stm_merge_finish(tx, &merge
# if OPERATION_LOGGING != OPLOG_NONE
    , e
# endif /* OPERATION_LOGGING != OPLOG_NONE */
    ))
      return merge.result;

    /* Update the previous operation */
    assert(merge.context.current.idx != e->parent.idx);
    merge.context.previous = merge.context.current;

    /* Set the conflict to the new return value */
    merge.context.leaf = 0;
# if OPERATION_LOGGING == OPLOG_FULL
    if (_tinystm.op_info.ids[e->id.idx].fi.rtype->type != FFI_TYPE_VOID)
      merge.context.conflict.previous_result = e->args[_tinystm.op_info.ids[e->id.idx].fi.nargs];
# endif /* OPERATION_LOGGING == OPLOG_FULL */
    merge.context.conflict.result = merge.context.rv;

# ifdef DEBUG_OP_LOG
    printf("==> merge %lu[%s] -> parent %lu[%s]\n", merge.context.current.idx, _tinystm.op_info.ids[GET_LOG_ENTRY(tx, merge.context.current.idx)->id.idx].name, e->parent.idx, _tinystm.op_info.ids[GET_LOG_ENTRY(tx, e->parent.idx)->id.idx].name);
# endif /* DEBUG_OP_LOG */

    /* Update the current operation */
    merge.context.current = e->parent;

    /* Clear the load position */
    merge.context.read = STM_INVALID_READ;
  }

  return merge.result;
}
#endif /* CM == CM_MERGE */

#if CM == CM_TIMESTAMP
/*
 * Oldest transaction has priority.
 */
stm_tx_policy_t
cm_timestamp(struct stm_tx *tx, const tx_conflict_t *conflict)
{
  PRINT_DEBUG("==> cm_timestamp(%p[%lu-%lu],%u,%lx,%lx)\n", tx, (unsigned long)tx->start, (unsigned long)tx->end, conflict->entries.type, conflict->entries.e1, conflict->entries.e2);

  if (tx->timestamp < conflict->other->timestamp)
    return STM_KILL_OTHER;
  if (tx->timestamp == conflict->other->timestamp && (uintptr_t)tx < (uintptr_t)conflict->other)
    return STM_KILL_OTHER;
  return STM_KILL_SELF | STM_DELAY;
}
#endif /* CM == CM_TIMESTAMP */

#if CM == CM_KARMA
/*
 * Transaction with more work done has priority.
 */
stm_tx_policy_t
cm_karma(struct stm_tx *tx, const tx_conflict_t *conflict)
{
  unsigned int me_work, other_work;

  PRINT_DEBUG("==> cm_karma(%p[%lu-%lu],%u,%lx,%lx)\n", tx, (unsigned long)tx->start, (unsigned long)tx->end, conflict->entries.type, conflict->entries.e1, conflict->entries.e2);

  me_work = (tx->w_set.nb_entries << 1) + tx->r_set.nb_entries;
  other_work = (conflict->other->w_set.nb_entries << 1) + conflict->other->r_set.nb_entries;

  if (me_work < other_work)
    return STM_KILL_OTHER;
  if (me_work == other_work && (uintptr_t)tx < (uintptr_t)conflict->other)
    return STM_KILL_OTHER;
  return STM_KILL_SELF;
}
#endif /* CM == CM_KARMA */

#if CM == CM_MERGE
/*
 * Merge conflict resolution.
 */
stm_tx_policy_t
cm_merge(struct stm_tx *tx, const tx_conflict_t *conflict)
{
# if defined(DEBUG) || defined(DEBUG_MERGE)
  printf("==> cm_merge(%p,%u,%lx,%lx)\n", tx, conflict->entries.type, conflict->entries.e1, conflict->entries.e2);
# endif /* DEBUG_MERGE */

  stm_tx_policy_t ret = STM_KILL_SELF;

  switch (conflict->entries.type) {
    case STM_RR_CONFLICT: {
# ifdef DEBUG_MERGE
      assert(ENTRY_VALID(conflict->entries.e1) && READ_VALID(tx, ENTRY_GET_READ(conflict->entries.e1)));
      r_entry_t *r = POINTER_FROM_READ(tx, ENTRY_GET_READ(conflict->entries.e1));
      assert(ENTRY_VALID(conflict->entries.e2) && WRITE_VALID(tx, ENTRY_GET_WRITE(conflict->entries.e2)));
      w_entry_t *w = POINTER_FROM_WRITE(tx, ENTRY_GET_WRITE(conflict->entries.e2));
      assert(r->lock == w->lock);
      printf("==> RR R%p = %lx, W%p[%lx] = %lx\n", r->addr, r->value, w->addr, w->mask, w->value);
#  if OPERATION_LOGGING != OPLOG_NONE
      if (OP_VALID(tx, r->op)) {
        op_entry_t *e = GET_LOG_ENTRY(tx, r->op.idx);
#   ifdef DEBUG_OP_LOG
        printf("==> RR R:%lx[%s]\n", e->id.idx, _tinystm.op_info.ids[e->id.idx].name);
#   else
        printf("==> RR R:%lx\n", e->id.idx);
#   endif /* DEBUG_OP_LOG */
      }
#  endif /* OPERATION_LOGGING != OPLOG_NONE */
#  if OPERATION_LOGGING == OPLOG_FULL
      if (OP_VALID(tx, w->op)) {
        op_entry_t *e = GET_LOG_ENTRY(w->tx, w->op.idx);
#   ifdef DEBUG_OP_LOG
        printf("==> RR W:%lx[%s]\n", e->id.idx, _tinystm.op_info.ids[e->id.idx].name);
#   else
        printf("==> RR W:%lx\n", e->id.idx);
#   endif /* DEBUG_OP_LOG */
      }
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
# endif /* DEBUG_MERGE */
    }
    break;
    case STM_RW_CONFLICT: {
# ifdef DEBUG_MERGE
      assert(!ENTRY_VALID(conflict->entries.e1) || READ_VALID(tx, ENTRY_GET_READ(conflict->entries.e1)));
      r_entry_t *r = ENTRY_VALID(conflict->entries.e1) ? POINTER_FROM_READ(tx, ENTRY_GET_READ(conflict->entries.e1)) : NULL;
      assert(!ENTRY_VALID(conflict->entries.e2) || WRITE_VALID(tx, ENTRY_GET_WRITE(conflict->entries.e2)));
      w_entry_unique_t *wu = ENTRY_VALID(conflict->entries.e2) ? POINTER_FROM_WRITE_UNIQUE(tx, ENTRY_GET_WRITE_UNIQUE(conflict->entries.e2)) : NULL;
      assert(!w || w->lock == r->lock);
      printf("==> RW R%p = %lx, W%p\n", r ? r->addr : NULL, r ? r->value : 0, w ? w->addr : NULL);
# endif /* DEBUG_MERGE */

# if DESIGN == WRITE_BACK_CTL
      /* With commit-time locking, read-write conflicts only occur during read validation, when an entry from our read set is locked for writing by another ongoing transaction. */
      // assert(w1->lock == w2->lock);

#  ifdef MERGE_LOCK_CONFLICT
      /* Unlock our locks and retry, triggering a subsequent read validation conflict. */
      if (tx->w_set_unique.nb_acquired > 0) {
        tx->revalidate |= REVALIDATE_RELOCK;
        int_stm_unlock(tx);
        ret = STM_RETRY;
      }
#  endif /* MERGE_LOCK_CONFLICT */
# endif /* DESIGN == WRITE_BACK_CTL */
    }
    break;
    case STM_WW_CONFLICT: {
# ifdef DEBUG_MERGE
      assert(ENTRY_VALID(conflict->entries.e1) && WRITE_VALID(tx, ENTRY_GET_WRITE(conflict->entries.e1)));
      w_entry_unique_t *wu1 = POINTER_FROM_WRITE_UNIQUE(tx, ENTRY_GET_WRITE_UNIQUE(conflict->entries.e1));
      assert(!ENTRY_VALID(conflict->entries.e2) || WRITE_VALID(tx, ENTRY_GET_WRITE(conflict->entries.e2)));
      w_entry_unique_t *wu2 = ENTRY_VALID(conflict->entries.e2) ? POINTER_FROM_WRITE_UNIQUE(tx, ENTRY_GET_WRITE_UNIQUE(conflict->entries.e2)) : NULL;
      assert(!wu2 || wu1->lock == wu2->lock);
      printf("==> WW W%p, W%p\n", wu1->addr, wu2 ? wu2->addr : NULL);
# endif /* DEBUG_MERGE */

# if DESIGN == WRITE_BACK_CTL
      /* With commit-time locking, write-write conflicts only occur during transaction commit, when an entry from our write set is locked for writing by another ongoing transaction. */
      // assert(w1->lock == w2->lock);
#  ifndef IRREVOCABLE_ENABLED
      assert(GET_STATUS(tx->status) == TX_COMMITTING);
#  endif /* IRREVOCABLE_ENABLED */

#  ifdef MERGE_LOCK_CONFLICT
      /* Unlock our locks and retry, potentially triggering a subsequent read validation conflict. */
      ret = STM_RETRY;
      if (tx->w_set_unique.nb_acquired > 0) {
        tx->revalidate |= REVALIDATE_RELOCK;
        int_stm_unlock(tx);
      }
#  endif /* MERGE_LOCK_CONFLICT */
# endif /* DESIGN == WRITE_BACK_CTL */
    }
    break;
    case STM_WR_CONFLICT: {
# ifdef DEBUG_MERGE
      assert(ENTRY_VALID(conflict->entries.e1) && WRITE_VALID(tx, ENTRY_GET_WRITE(conflict->entries.e1)));
      w_entry_t *w = POINTER_FROM_WRITE(tx, ENTRY_GET_WRITE(conflict->entries.e1));
      assert(ENTRY_VALID(conflict->entries.e2) && READ_VALID(tx, ENTRY_GET_READ(conflict->entries.e2)));
      r_entry_t *r = POINTER_FROM_READ(tx, ENTRY_GET_READ(conflict->entries.e2));
      assert(w->lock == r->lock);
      printf("==> WR W%p[%lx] = %lx, R%p = %lx\n", w->addr, w->mask, w->value, r->addr, r->value);
# endif /* DEBUG_MERGE */
    }
    break;
    case STM_RD_VALIDATE: {
      assert(ENTRY_VALID(conflict->entries.e1) && READ_VALID(tx, ENTRY_GET_READ(conflict->entries.e1)));
#if OPERATION_LOGGING != OPLOG_NONE
      r_entry_t *r = POINTER_FROM_READ(tx, ENTRY_GET_READ(conflict->entries.e1));
#endif /* OPERATION_LOGGING != OPLOG_NONE */
#if DETECTION == TIME_BASED && (!defined(READ_SET_DETAILED) || !defined(READ_SET_SOURCE))
      assert(!ENTRY_VALID(conflict->entries.e2) || (ENTRY_VALID(conflict->entries.e2) && WRITE_VALID(tx, ENTRY_GET_WRITE(conflict->entries.e2))));
#endif /* (DETECTION == TIME_BASED && (! READ_SET_DETAILED || ! READ_SET_SOURCE)) */
# ifdef DEBUG_MERGE
      w_entry_t *w = ENTRY_VALID(conflict->entries.e2) ? POINTER_FROM_WRITE(tx, ENTRY_GET_WRITE(conflict->entries.e2)) : NULL;
      assert(!w || (w && w->addr == r->addr && w->lock == r->lock));
      if (w)
        printf("==> RV R%p = %lx, W%p[%lx] = %lx, M%p = %lx\n", r->addr, r->value, w->addr, w->mask, w->value, r->addr, ATOMIC_LOAD(r->addr));
      else
        printf("==> RV R%p = %lx, M%p = %lx\n", r->addr, r->value, r->addr, ATOMIC_LOAD(r->addr));

#  if OPERATION_LOGGING != OPLOG_NONE
      if (OP_VALID(tx, r->op)) {
        op_entry_t *e = GET_LOG_ENTRY(tx, r->op.idx);
#   ifdef DEBUG_OP_LOG
        printf("==> RV R:%lx[%s]\n", e->id.idx, _tinystm.op_info.ids[e->id.idx].name);
#   else
        printf("==> RV R:%lx\n", e->id.idx);
#   endif /* DEBUG_OP_LOG */
      }
#  endif /* OPERATION_LOGGING != OPLOG_NONE */
#  if OPERATION_LOGGING == OPLOG_FULL
      if (w && OP_VALID(tx, w->op)) {
        op_entry_t *e = GET_LOG_ENTRY(w->tx, w->op.idx);
#   ifdef DEBUG_OP_LOG
        printf("==> RV W:%lx[%s]\n", e->id.idx, _tinystm.op_info.ids[e->id.idx].name);
#   else
        printf("==> RV W:%lx\n", e->id.idx);
#   endif /* DEBUG_OP_LOG */
      }
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
# endif /* DEBUG_MERGE */

# if DESIGN == WRITE_BACK_CTL
      /* With commit-time locking, read validation conflicts only occur when we read a stale value; an entry from our read set has a timestamp that doesn't match the current timestamp (from memory or from the write set) for the address. */
      // assert((w && LOCK_GET_OWNED(l) && w == (w_entry_t *)(LOCK_GET_ADDR(l)) && r->version != w->version) || (!w && !LOCK_GET_OWNED(l) && r->version != LOCK_GET_TIMESTAMP(l)));

#if OPERATION_LOGGING != OPLOG_NONE && defined(DEBUG_OP_LOG)
      if (OP_VALID(tx, r->op)) {
        size_t idx = r->op.idx;
        printf("\nops: ");
        while (idx != STM_BAD_IDX) {
          assert(idx <= tx->op_log.size);
          op_entry_t *e = GET_LOG_ENTRY(tx, idx);
          assert(e->id.idx < _tinystm.op_info.nb_ids);
          printf(tx->merge.context && idx == tx->merge.context->current.idx ? "%ld[%s]* " : "%ld[%s] ", idx, _tinystm.op_info.ids[e->id.idx].name);
          assert(idx != e->parent.idx);
          idx = e->parent.idx;
        }
        printf("\n");
      }
#endif /* OPERATION_LOGGING && DEBUG_OP_LOG */

      if (
#  if OPERATION_LOGGING != OPLOG_NONE
          OP_VALID(tx, r->op)
#  else
          1
#  endif /* OPERATION_LOGGING != OPLOG_NONE */
          && int_stm_merge_ok(tx)
      ) {

        /* Deduplicate this entry */
        int_stm_dedup(tx, READ_FROM_POINTER(tx, r));

#  ifdef MERGE_UNLOCK
        /* Unlock our locks before merging. */
        if (tx->w_set_unique.nb_acquired > 0)
          int_stm_unlock(tx);
#  endif /* MERGE_UNLOCK */

        switch (stm_merge(tx, &conflict->entries)) {
          case STM_MERGE_OK:
            ret = STM_SKIP;
          break;
          case STM_MERGE_RETRY:
            ret = STM_RETRY;
          break;
          case STM_MERGE_ABORT:
            ret = STM_KILL_SELF;
          break;
          default:
            ret = STM_KILL_SELF;
          break;
        }
      }
# endif /* DESIGN == WRITE_BACK_CTL */
    }
    break;

    case STM_WR_VALIDATE: {
      assert(ENTRY_VALID(conflict->entries.e1) && READ_VALID(tx, ENTRY_GET_READ(conflict->entries.e1)));
# ifdef DEBUG_MERGE
      r_entry_t *r = POINTER_FROM_READ(tx, ENTRY_GET_READ(conflict->entries.e1));
      assert(r->lock);
      stm_word_t v = ATOMIC_LOAD(r->addr);
      printf("==> WV R%p = %lx, M%p = %lx\n", r->addr, r->value, r->addr, v);

#  if OPERATION_LOGGING != OPLOG_NONE
      if (OP_VALID(tx, r->op)) {
        op_entry_t *e = GET_LOG_ENTRY(tx, r->op.idx);
#   if defined(DEBUG_OP_LOG)
        printf("==> WV R:%lx[%s]\n", e->id.idx, _tinystm.op_info.ids[e->id.idx].name);
#   else
        printf("==> WV R:%lx\n", e->id.idx);
#   endif /* DEBUG_OP_LOG */
      }
#  endif /* OPERATION_LOGGING != OPLOG_NONE */
# endif /* DEBUG_MERGE */
    }
    break;
    default:
      return ret;
    break;
  }

  return ret;
}
#endif /* CM == CM_MERGE */

#ifdef SIGNAL_HANDLER
/*
 * Catch signal (to emulate non-faulting load).
 */
static void
signal_catcher(int sig)
{
  sigset_t block_signal;
  stm_tx_t *tx = tls_get_tx();

  /* A fault might only occur upon a load concurrent with a free (read-after-free) */
  PRINT_DEBUG("Caught signal: %d\n", sig);

  /* TODO: TX_KILLED should be also allowed */
  if (tx == NULL || tx->attr.no_retry || GET_STATUS(tx->status) != TX_ACTIVE_BIT) {
    /* There is not much we can do: execution will restart at faulty load */
    fprintf(stderr, "Error: invalid memory accessed and no longjmp destination\n");
    exit(1);
  }

  /* Unblock the signal since there is no return to signal handler */
  sigemptyset(&block_signal);
  sigaddset(&block_signal, sig);
  pthread_sigmask(SIG_UNBLOCK, &block_signal, NULL);

  /* Will cause a longjmp */
  stm_rollback(tx, STM_ABORT_SIGNAL);
}
#endif /* SIGNAL_HANDLER */

/* ################################################################### *
 * STM FUNCTIONS
 * ################################################################### */

/*
 * Called once (from main) to initialize STM infrastructure.
 */
_CALLCONV void
stm_init()
{
#if DESIGN == WRITE_BACK_ETL_VR
  char *s;
#endif /* DESIGN == WRITE_BACK_ETL */
#ifdef SIGNAL_HANDLER
  struct sigaction act;
#endif /* SIGNAL_HANDLER */

  PRINT_DEBUG("==> stm_init()\n");

  if (_tinystm.initialized)
    return;

  PRINT_DEBUG("\tsizeof(word)=%d\n", (int)sizeof(stm_word_t));

  PRINT_DEBUG("\tVERSION_MAX=0x%lx\n", (unsigned long)VERSION_MAX);

  COMPILE_TIME_ASSERT(sizeof(stm_word_t) == sizeof(void *));

#if MEMORY_MANAGEMENT != MM_NONE
  gc_init(stm_get_clock);
#endif /* MEMORY_MANAGEMENT != MM_NONE */

#if DESIGN == WRITE_BACK_ETL_VR
  s = getenv(VR_THRESHOLD);
  if (s != NULL)
    _tinystm.vr_threshold = (int)strtol(s, NULL, 10);
  else
    _tinystm.vr_threshold = VR_THRESHOLD_DEFAULT;
  PRINT_DEBUG("\tVR_THRESHOLD=%d\n", _tinystm.vr_threshold);
#endif /* DESIGN == WRITE_BACK_ETL_VR */

  /* Set locks and clock but should be already to 0 */
#if DETECTION == TIME_BASED
  memset((void *)_tinystm.locks, 0, LOCK_ARRAY_SIZE * sizeof(*_tinystm.locks));
#endif /* DETECTION == TIME_BASED */
  CLOCK = 0;

  stm_quiesce_init();

  tls_init();

#ifdef TM_STATISTICS
  if (getenv("TM_STATISTICS") != NULL)
    mod_stats_init();
#endif /* TM_STATISTICS */

#ifdef SIGNAL_HANDLER
  if (getenv(NO_SIGNAL_HANDLER) == NULL) {
    /* Catch signals for non-faulting load */
    act.sa_handler = signal_catcher;
    act.sa_flags = 0;
    sigemptyset(&act.sa_mask);
    if (sigaction(SIGBUS, &act, NULL) < 0 || sigaction(SIGSEGV, &act, NULL) < 0) {
      perror("sigaction");
      exit(1);
    }
  }
#endif /* SIGNAL_HANDLER */

  _tinystm.initialized = 1;
}

/*
 * Called once (from main) to clean up STM infrastructure.
 */
_CALLCONV void
stm_exit(void)
{
  PRINT_DEBUG("==> stm_exit()\n");

  if (!_tinystm.initialized)
    return;

#ifdef DEBUG_ABORT
  debug_end(debug);
#endif /* DEBUG_ABORT */

  tls_exit();
  stm_quiesce_exit();

#if MEMORY_MANAGEMENT != MM_NONE
  gc_exit();
#endif /* MEMORY_MANAGEMENT != MM_NONE */

#ifdef TM_STATISTICS
  /* Display statistics before to lose it */
  if (getenv("TM_STATISTICS") != NULL) {
    unsigned long long ull;
    unsigned long u[16];
    if (stm_get_global_stats("global_nb_rs_entries", &u[0]) != 0)
      printf("Read Set: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_rs_entries_aborted", &u[0]) != 0)
      printf("Read Set Aborted: %lu\n", u[0]);
    if (stm_get_global_stats("global_max_rs_entries", &u[0]) != 0)
      printf("Max Read Set: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_ws_entries", &u[0]) != 0)
      printf("Write Set: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_ws_entries_aborted", &u[0]) != 0)
      printf("Write Set Aborted: %lu\n", u[0]);
    if (stm_get_global_stats("global_max_ws_entries", &u[0]) != 0)
      printf("Max Write Set: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_ws_unique_entries", &u[0]) != 0)
      printf("Write Set Unique: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_ws_unique_entries_aborted", &u[0]) != 0)
      printf("Write Set Unique Aborted: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_ws_unique_entries_nonempty", &u[0]) != 0)
      printf("Write Set Unique Nonempty: %lu\n", u[0]);
    if (stm_get_global_stats("global_max_ws_unique_entries", &u[0]) != 0)
      printf("Max Write Set Unique: %lu\n", u[0]);
    if (stm_get_global_stats("global_ol_used", &u[0]) != 0)
      printf("Operation Log: %lu\n", u[0]);
    if (stm_get_global_stats("global_ol_used_aborted", &u[0]) != 0)
      printf("Operation Log Aborted: %lu\n", u[0]);
    if (stm_get_global_stats("global_max_ol_used", &u[0]) != 0)
      printf("Max Operation Log: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_rb_entries_aborted", &u[0]) != 0)
      printf("Rollback Aborted: %lu\n", u[0]);
    if (stm_get_global_stats("global_max_rb_entries", &u[0]) != 0)
      printf("Max Rollback: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_extensions", &u[0]) != 0)
      printf("Extensions: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_commits", &u[0]) != 0)
      printf("Commits: %lu\n", u[0]);
    if (stm_get_global_stats("global_work_committed", &ull) != 0)
      printf("Committed Work: %llu\n", ull);
    if (stm_get_global_stats("global_nb_aborts", &u[0]) != 0)
      printf("Aborts: %lu\n", u[0]);
    if (stm_get_global_stats("global_work_aborted", &ull) != 0)
      printf("Aborted Work: %llu\n", ull);
    if (stm_get_global_stats("global_work_merge_before", &ull) != 0)
      printf("Work before Merge: %llu\n", ull);
    if (stm_get_global_stats("global_work_merge_after", &ull) != 0)
      printf("Work after Merge: %llu\n", ull);
    if (stm_get_global_stats("global_work_first_order", &ull) != 0)
      printf("First Order Work: %lld\n", (long long)ull);
    if (stm_get_global_stats("global_nb_relocks", &u[0]) != 0)
      printf("Relocks: %lu\n", u[0]);
    if (stm_get_global_stats("global_max_retries", &u[0]) != 0)
      printf("Max Retries: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_merges_manual", &u) != 0)
      printf("Merges (Manual): %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_merges_replay", &u) != 0)
      printf("Merges (Replay): %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_merges_ok", &u) != 0)
      printf("Merges (OK): %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_merges_retry", &u) != 0)
      printf("Merges (Retry): %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_reads", &u) != 0)
      printf("Reads: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_writes", &u) != 0)
      printf("Writes: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_reverted_reads", &u[0]) != 0)
      printf("Reads Reverted: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_reverted_writes", &u[0]) != 0)
      printf("Writes Reverted: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_reverted_ops", &u[0]) != 0)
      printf("Operations Reverted: %lu\n", u[0]);
    if (stm_get_global_stats("global_nb_aborts_reason", &u) != 0) {
      for (unsigned i = 0; i < 16; ++i) {
        switch (i) {
          case 0: printf("Unknown"); break;
          case 1: printf("Read-Read"); break;
          case 2: printf("Read-Write"); break;
          case 3: printf("Write-Read"); break;
          case 4: printf("Write-Write"); break;
          case 5: printf("Read Validate"); break;
          case 6: printf("Write Validate"); break;
          case 7: printf("Commit Validate"); break;
          case 8: printf("Irrevocable TX"); break;
          case 9: printf("Manual Abort"); break;
          case 10: printf("Killed TX"); break;
          case 11: printf("Signal"); break;
          case 12: printf("Write-Size Extend"); break;
          case 13: printf("Merged TX Commit"); break;
          case 14: printf("Merged TX Abort"); break;
          case 15: printf("Other"); break;
        }
        printf(": %lu\n", u[i]);
      }
    }
    if (stm_get_global_stats("max_history", &ull) != 0 && ull <= sizeof(u) / sizeof(*u)) {
      if (stm_get_global_stats("global_nb_commits_merges", &u) != 0) {
        for (unsigned i = 0; i < ull; ++i)
          printf("Commits - Merges Ok %d: %lu\n", i, u[i]);
      }
      if (stm_get_global_stats("global_nb_aborts_merges", &u) != 0) {
        for (unsigned i = 0; i < ull; ++i)
          printf("Aborts - Merges Ok %d: %lu\n", i, u[i]);
      }
    }

# if CM == CM_MERGE && defined(MERGE_FEEDBACK)
    for (unsigned int i = 0; i < _tinystm.op_info.nb_ids; ++i) {
      if (_tinystm.op_info.ids[i].repairs_attempted || _tinystm.op_info.ids[i].repairs_ok || _tinystm.op_info.ids[i].aborted_tx || _tinystm.op_info.ids[i].committed_tx)
        printf("Operation %d (%s): Enabled: %d, Repairs Attempted: %ld, Repairs Succeeded: %ld, Aborted TX: %ld, Committed TX: %ld\n", i, _tinystm.op_info.ids[i].name, _tinystm.op_info.ids[i].enabled, _tinystm.op_info.ids[i].repairs_attempted, _tinystm.op_info.ids[i].repairs_ok, _tinystm.op_info.ids[i].aborted_tx, _tinystm.op_info.ids[i].committed_tx);
    }
# endif /* CM == CM_MERGE && MERGE_FEEDBACK */
  }
#endif /* TM_STATISTICS */

#if OPERATION_LOGGING != OPLOG_NONE
  xfree(_tinystm.op_info.ids);
#endif /* OPERATION_LOGGING != OPLOG_NONE */

  _tinystm.initialized = 0;
}

/*
 * Called by the CURRENT thread to initialize thread-local STM data.
 */
_CALLCONV stm_tx_t *
stm_init_thread(void)
{
  return int_stm_init_thread();
}

/*
 * Called by the CURRENT thread to cleanup thread-local STM data.
 */
_CALLCONV void
stm_exit_thread(void)
{
  TX_GET;
  int_stm_exit_thread(tx);
}

_CALLCONV void
stm_exit_thread_tx(stm_tx_t *tx)
{
  int_stm_exit_thread(tx);
}

/*
 * Called by the CURRENT thread to start a transaction.
 */
_CALLCONV sigjmp_buf *
stm_start(stm_tx_attr_t attr)
{
  TX_GET;
  return int_stm_start(tx, attr);
}

_CALLCONV sigjmp_buf *
stm_start_tx(stm_tx_t *tx, stm_tx_attr_t attr)
{
  return int_stm_start(tx, attr);
}

/*
 * Called by the CURRENT thread to commit a transaction.
 */
_CALLCONV int
stm_commit(void)
{
  TX_GET;
  return int_stm_commit(tx);
}

_CALLCONV int
stm_commit_tx(stm_tx_t *tx)
{
  return int_stm_commit(tx);
}

/*
 * Called by the CURRENT thread to abort a transaction.
 */
_CALLCONV void
stm_abort(unsigned int reason)
{
  TX_GET;
  stm_rollback(tx, reason | STM_ABORT_EXPLICIT);
}

_CALLCONV void
stm_abort_tx(stm_tx_t *tx, unsigned int reason)
{
  stm_rollback(tx, reason | STM_ABORT_EXPLICIT);
}

_CALLCONV void
stm_stop(unsigned int reason)
{
  TX_GET;
  stm_cleanup(tx, reason | STM_ABORT_EXPLICIT);
}

_CALLCONV int
stm_revalidate()
{
  TX_GET;
  return int_stm_revalidate(tx);
}

/*
 * Called by the CURRENT thread to load a word-sized value.
 */
_CALLCONV ALIGNED stm_word_t
stm_load(const stm_word_t *addr)
{
  TX_GET;
  return stm_load_tx(tx, addr);
}

_CALLCONV stm_word_t
stm_load_tx(stm_tx_t *tx, const stm_word_t *addr)
{
#ifdef READ_SET_TAGGED
  return int_stm_load(tx, addr, 0);
#else
  return int_stm_load(tx, addr);
#endif /* READ_SET_TAGGED */
}

_CALLCONV ALIGNED stm_word_t
stm_load_tag(const stm_word_t *addr, const uintptr_t tag)
{
  TX_GET;
  return stm_load_tag_tx(tx, addr, tag);
}

_CALLCONV stm_word_t
stm_load_tag_tx(struct stm_tx *tx, const stm_word_t *addr, const uintptr_t tag)
{
#ifdef READ_SET_TAGGED
  return int_stm_load(tx, addr, tag);
#else
  return int_stm_load(tx, addr);
#endif /* READ_SET_TAGGED */
}

/*
 * Called by the CURRENT thread to store a word-sized value.
 */
_CALLCONV ALIGNED void
stm_store(stm_word_t *addr, const stm_word_t value)
{
  TX_GET;
  stm_store_tx(tx, addr, value);
}

_CALLCONV void
stm_store_tx(stm_tx_t *tx, stm_word_t *addr, const stm_word_t value)
{
  int_stm_store(tx, addr, value);
}

/*
 * Called by the CURRENT thread to store part of a word-sized value.
 */
_CALLCONV ALIGNED void
stm_store2(stm_word_t *addr, const stm_word_t value, const stm_word_t mask)
{
  TX_GET;
  stm_store2_tx(tx, addr, value, mask);
}

_CALLCONV void
stm_store2_tx(stm_tx_t *tx, stm_word_t *addr, const stm_word_t value, const stm_word_t mask)
{
  int_stm_store2(tx, addr, value, mask);
}

/*
 * Called by the CURRENT thread to inquire about the status of a transaction.
 */
_CALLCONV int
stm_active(void)
{
  TX_GET;
  return stm_active_tx(tx);
}

_CALLCONV int
stm_active_tx(const stm_tx_t *tx)
{
  return int_stm_active(tx);
}

/*
 * Called by the CURRENT thread to inquire about the status of a transaction.
 */
_CALLCONV int
stm_aborted(void)
{
  TX_GET;
  return stm_aborted_tx(tx);
}

_CALLCONV int
stm_aborted_tx(const stm_tx_t *tx)
{
  return int_stm_aborted(tx);
}

/*
 * Called by the CURRENT thread to inquire about the status of a transaction.
 */
_CALLCONV int
stm_committing(void)
{
  TX_GET;
  return stm_committing_tx(tx);
}

_CALLCONV int
stm_committing_tx(const stm_tx_t *tx)
{
  return int_stm_committing(tx);
}

/*
 * Called by the CURRENT thread to inquire about the status of a transaction.
 */
_CALLCONV int
stm_irrevocable(void)
{
  TX_GET;
  return stm_irrevocable_tx(tx);
}

_CALLCONV int
stm_irrevocable_tx(const stm_tx_t *tx)
{
  return int_stm_irrevocable(tx);
}

/*
 * Called by the CURRENT thread to inquire about the status of a transaction.
 */
_CALLCONV int
stm_killed(void)
{
  TX_GET;
  return stm_killed_tx(tx);
}

_CALLCONV int
stm_killed_tx(const stm_tx_t *tx)
{
  return int_stm_killed(tx);
}

/*
 * Called by the CURRENT thread to obtain an environment for setjmp/longjmp.
 */
_CALLCONV sigjmp_buf *
stm_get_env(void)
{
  TX_GET;
  return stm_get_env_tx(tx);
}

_CALLCONV sigjmp_buf *
stm_get_env_tx(stm_tx_t *tx)
{
  return int_stm_get_env(tx);
}

/*
 * Get transaction attributes.
 */
_CALLCONV stm_tx_attr_t
stm_get_attributes(void)
{
  TX_GET;
  return stm_get_attributes_tx(tx);
}

/*
 * Get transaction attributes from a specifc transaction.
 */
_CALLCONV stm_tx_attr_t
stm_get_attributes_tx(const struct stm_tx *tx)
{
  assert (tx != NULL);
  return tx->attr;
}

/*
 * Return statistics about a thread/transaction.
 */
_CALLCONV int
stm_get_stats(const stm_stats_t name, void *val)
{
  TX_GET;
  return stm_get_stats_tx(tx, name, val);
}

_CALLCONV int
stm_get_stats_tx(const stm_tx_t *tx, const stm_stats_t name, void *val)
{
  return int_stm_get_stats(tx, name, val);
}

/*
 * Return STM parameters.
 */
_CALLCONV int
stm_get_parameter(const char *name, void *val)
{
  if (strcmp("contention_manager", name) == 0) {
    *(const char **)val = cm_names[CM];
    return 1;
  }
  if (strcmp("design", name) == 0) {
    *(const char **)val = design_names[DESIGN];
    return 1;
  }
  if (strcmp("initial_r_set_size", name) == 0) {
    *(int *)val = R_SET_SIZE;
    return 1;
  }
  if (strcmp("initial_w_set_size", name) == 0) {
    *(int *)val = W_SET_SIZE;
    return 1;
  }
#if OPERATION_LOGGING != OPLOG_NONE
  if (strcmp("initial_op_log_size", name) == 0) {
    *(int *)val = OP_LOG_SIZE;
    return 1;
  }
#endif /* OPERATION_LOGGING != OPLOG_NONE */
#if CM == CM_BACKOFF
  if (strcmp("min_backoff", name) == 0) {
    *(unsigned long *)val = MIN_BACKOFF;
    return 1;
  }
  if (strcmp("max_backoff", name) == 0) {
    *(unsigned long *)val = MAX_BACKOFF;
    return 1;
  }
#endif /* CM == CM_BACKOFF */
#if DESIGN == WRITE_BACK_ETL_VR
  if (strcmp("vr_threshold", name) == 0) {
    *(int *)val = _tinystm.vr_threshold;
    return 1;
  }
#endif /* DESIGN == WRITE_BACK_ETL_VR */
#ifdef COMPILE_FLAGS
  if (strcmp("compile_flags", name) == 0) {
    *(const char **)val = XSTR(COMPILE_FLAGS);
    return 1;
  }
#endif /* COMPILE_FLAGS */
  return 0;
}

/*
 * Set STM parameters.
 */
_CALLCONV int
stm_set_parameter(const char *name, void *val)
{
#ifdef CONFLICT_TRACKING
  if (strcmp("cm_function", name) == 0) {
    _tinystm.conflict_cb = (const stm_tx_policy_t (*)(const stm_tx_t *, const tx_conflict_t *))val;
  }
#endif /* CONFLICT_TRACKING */
#if DESIGN == WRITE_BACK_ETL_VR
  if (strcmp("vr_threshold", name) == 0) {
    _tinystm.vr_threshold = *(int *)val;
    return 1;
  }
# endif /* DESIGN == WRITE_BACK_ETL_VR */
  return 0;
}

/*
 * Create transaction-specific data (return -1 on error).
 */
_CALLCONV int
stm_create_specific(void)
{
  if (_tinystm.nb_specific >= MAX_SPECIFIC) {
    fprintf(stderr, "Error: maximum number of specific slots reached\n");
    return -1;
  }
  return _tinystm.nb_specific++;
}

/*
 * Store transaction-specific data.
 */
_CALLCONV void
stm_set_specific(const int key, const void *data)
{
  TX_GET;
  stm_set_specific_tx(tx, key, data);
}

/*
 * Store transaction-specific data to a specifc transaction.
 */
_CALLCONV void
stm_set_specific_tx(stm_tx_t *tx, const int key, const void *data)
{
  int_stm_set_specific(tx, key, data);
}


/*
 * Fetch transaction-specific data.
 */
_CALLCONV void *
stm_get_specific(const int key)
{
  TX_GET;
  return stm_get_specific_tx(tx, key);
}

/*
 * Fetch transaction-specific data from a specific transaction.
 */
_CALLCONV void *
stm_get_specific_tx(const stm_tx_t *tx, const int key)
{
  return int_stm_get_specific(tx, key);
}

/*
 * Register callbacks for an external module (must be called before creating transactions).
 */
_CALLCONV int
stm_register(void (* const on_thread_init)(struct stm_tx *tx, const void *arg),
             void (* const on_thread_exit)(const struct stm_tx *tx, const void *arg),
             void (* const on_start)(const struct stm_tx *tx, const void *arg),
             void (* const on_precommit)(const struct stm_tx *tx, const void *arg),
             void (* const on_commit)(const struct stm_tx *tx, const void *arg),
             void (* const on_abort)(const struct stm_tx *tx, const stm_tx_abort_t reason, const void *arg),
             void *arg)
{
  if ((on_thread_init != NULL && _tinystm.nb_init_cb >= MAX_CB) ||
      (on_thread_exit != NULL && _tinystm.nb_exit_cb >= MAX_CB) ||
      (on_start != NULL && _tinystm.nb_start_cb >= MAX_CB) ||
      (on_precommit != NULL && _tinystm.nb_precommit_cb >= MAX_CB) ||
      (on_commit != NULL && _tinystm.nb_commit_cb >= MAX_CB) ||
      (on_abort != NULL && _tinystm.nb_abort_cb >= MAX_CB)) {
    fprintf(stderr, "Error: maximum number of modules reached\n");
    return 0;
  }
  /* New callback */
  if (on_thread_init != NULL) {
    _tinystm.init_cb[_tinystm.nb_init_cb].f = on_thread_init;
    _tinystm.init_cb[_tinystm.nb_init_cb++].arg = arg;
  }
  /* Delete callback */
  if (on_thread_exit != NULL) {
    _tinystm.exit_cb[_tinystm.nb_exit_cb].f = on_thread_exit;
    _tinystm.exit_cb[_tinystm.nb_exit_cb++].arg = arg;
  }
  /* Start callback */
  if (on_start != NULL) {
    _tinystm.start_cb[_tinystm.nb_start_cb].f = on_start;
    _tinystm.start_cb[_tinystm.nb_start_cb++].arg = arg;
  }
  /* Pre-commit callback */
  if (on_precommit != NULL) {
    _tinystm.precommit_cb[_tinystm.nb_precommit_cb].f = on_precommit;
    _tinystm.precommit_cb[_tinystm.nb_precommit_cb++].arg = arg;
  }
  /* Commit callback */
  if (on_commit != NULL) {
    _tinystm.commit_cb[_tinystm.nb_commit_cb].f = on_commit;
    _tinystm.commit_cb[_tinystm.nb_commit_cb++].arg = arg;
  }
  /* Abort callback */
  if (on_abort != NULL) {
    _tinystm.abort_cb[_tinystm.nb_abort_cb].f = on_abort;
    _tinystm.abort_cb[_tinystm.nb_abort_cb++].arg = arg;
  }

  return 1;
}

/*
 * Called by the CURRENT thread to load a word-sized value in a unit transaction.
 */
_CALLCONV stm_word_t
stm_unit_load(stm_word_t *addr, stm_word_t *timestamp)
{
#ifdef UNIT_TX
  stm_lock_t *lock;
  stm_version_t l, l2;
  stm_word_t value;

  PRINT_DEBUG2("==> stm_unit_load(a=%p)\n", addr);

  /* Get reference to lock */
  lock = GET_LOCK(addr);

  /* Read lock, value, lock */
 restart:
  l = LOCK_READ_ACQ(lock);
 restart_no_load:
  if (LOCK_GET_OWNED(l)) {
    /* Locked: wait until lock is free */
#ifdef WAIT_YIELD
    sched_yield();
#endif /* WAIT_YIELD */
    goto restart;
  }
  /* Not locked */
  value = ATOMIC_LOAD_ACQ(addr);
  l2 = LOCK_READ_ACQ(lock);
  if (l != l2) {
    l = l2;
    goto restart_no_load;
  }

  if (timestamp != NULL)
    *timestamp = LOCK_GET_TIMESTAMP(l);

  return value;
#else /* ! UNIT_TX */
  fprintf(stderr, "Unit transaction is not enabled\n");
  exit(-1);
  return 1;
#endif /* ! UNIT_TX */
}

/*
 * Store a word-sized value in a unit transaction.
 */
static INLINE int
stm_unit_write(stm_word_t *addr, stm_word_t value, stm_word_t mask, stm_word_t *timestamp)
{
#ifdef UNIT_TX
  stm_lock_t *lock;
  stm_version_t l;

  PRINT_DEBUG2("==> stm_unit_write(a=%p,d=%p-%lu,m=0x%lx)\n",
               addr, (void *)value, (unsigned long)value, (unsigned long)mask);

  /* Get reference to lock */
  lock = GET_LOCK(addr);

  /* Try to acquire lock */
 restart:
  l = LOCK_READ_ACQ(lock);
  if (LOCK_GET_OWNED(l)) {
    /* Locked: wait until lock is free */
#ifdef WAIT_YIELD
    sched_yield();
#endif /* WAIT_YIELD */
    goto restart;
  }
  /* Not locked */
  if (timestamp != NULL && LOCK_GET_TIMESTAMP(l) > *timestamp) {
    /* Return current timestamp */
    *timestamp = LOCK_GET_TIMESTAMP(l);
    return 0;
  }
  /* TODO: would need to store thread ID to be able to kill it (for wait freedom) */
  if (LOCK_WRITE_CAS(lock, l, LOCK_UNIT) == 0)
    goto restart;
  ATOMIC_STORE(addr, value);
  /* Update timestamp with newer value (may exceed VERSION_MAX by up to MAX_THREADS) */
  l = FETCH_INC_CLOCK + 1;
  if (timestamp != NULL)
    *timestamp = l;
  /* Make sure that lock release becomes visible */
  LOCK_STORE_REL(lock, LOCK_SET_TIMESTAMP(l));
  if (unlikely(l >= VERSION_MAX)) {
    /* Block all transactions and reset clock (current thread is not in active transaction) */
    stm_quiesce_barrier(NULL, rollover_clock, NULL);
  }
  return 1;
#else /* ! UNIT_TX */
  fprintf(stderr, "Unit transaction is not enabled\n");
  exit(-1);
  return 1;
#endif /* ! UNIT_TX */
}

/*
 * Called by the CURRENT thread to store a word-sized value in a unit transaction.
 */
_CALLCONV int
stm_unit_store(stm_word_t *addr, stm_word_t value, stm_word_t *timestamp)
{
  return stm_unit_write(addr, value, ~(stm_word_t)0, timestamp);
}

/*
 * Called by the CURRENT thread to store part of a word-sized value in a unit transaction.
 */
_CALLCONV int
stm_unit_store2(stm_word_t *addr, stm_word_t value, stm_word_t mask, stm_word_t *timestamp)
{
  return stm_unit_write(addr, value, mask, timestamp);
}

/*
 * Enable or disable extensions and set upper bound on snapshot.
 */
static INLINE void
int_stm_set_extension(stm_tx_t *tx, int enable, stm_word_t *timestamp)
{
#ifdef UNIT_TX
  tx->attr.no_extend = !enable;
  if (timestamp != NULL && *timestamp < tx->end)
    tx->end = *timestamp;
#else /* ! UNIT_TX */
  fprintf(stderr, "Unit transaction is not enabled\n");
  exit(-1);
#endif /* ! UNIT_TX */
}

_CALLCONV void
stm_set_extension(int enable, stm_word_t *timestamp)
{
  TX_GET;
  stm_set_extension_tx(tx, enable, timestamp);
}

_CALLCONV void
stm_set_extension_tx(stm_tx_t *tx, int enable, stm_word_t *timestamp)
{
  int_stm_set_extension(tx, enable, timestamp);
}

/*
 * Get curent value of global clock.
 */
_CALLCONV const stm_word_t
stm_get_clock(void)
{
  return GET_CLOCK;
}

/*
 * Get current transaction descriptor.
 */
_CALLCONV stm_tx_t *
stm_current_tx(void)
{
  return tls_get_tx();
}

_CALLCONV const stm_features_t
stm_get_features() {
  return 0
#if CM == CM_MERGE
  | STM_FEATURE_MERGE
#endif /* CM == CM_MERGE */
#ifdef READ_SET_SOURCE
  | STM_FEATURE_READ_SET_SOURCE
#endif /* READ_SET_SOURCE */
#if OPERATION_LOGGING == OPLOG_FULL
  | STM_FEATURE_OPLOG_FULL
#endif /* OPERATION_LOGGING */
  ;
}

_CALLCONV const stm_op_id_t
stm_new_opcode(const char *s, const ffi_cif *fi, void (*f)(), const stm_merge_cb_t delayed, const stm_merge_policy_t policy[2]) {
  stm_op_id_t id = STM_INVALID_OPID;
# if defined(DEBUG_OP_LOG) || defined (DEBUG)
  printf("==> stm_new_opcode(%s,%p,%p,%p) = %ld\n", s, fi, f, delayed, _tinystm.op_info.nb_ids);
# endif /* DEBUG_OP_LOG || DEBUG */

# if OPERATION_LOGGING != OPLOG_NONE
  if (unlikely(_tinystm.op_info.ids == NULL)) {
    /* Allocate operation table */
    _tinystm.op_info.size = OP_INFO_SIZE;
    _tinystm.op_info.ids = (op_info_t *)xmalloc_aligned(_tinystm.op_info.size * sizeof(op_info_t));
  } else if (unlikely(_tinystm.op_info.nb_ids == _tinystm.op_info.size)) {
    /* Extend operation table */
    _tinystm.op_info.size *= 2;
    _tinystm.op_info.ids = (op_info_t *)xrealloc(_tinystm.op_info.ids, _tinystm.op_info.size * sizeof(op_info_t));
  }

  id.idx = _tinystm.op_info.nb_ids++;
  op_info_t *o = &_tinystm.op_info.ids[id.idx];
#  if defined(DEBUG_OP_LOG) || defined(MERGE_FEEDBACK)
  strncpy(o->name, s, OP_NAME_SIZE);
  o->name[OP_NAME_SIZE - 1] = '\0';
#  endif /* DEBUG_OP_LOG || MERGE_FEEDBACK */
  o->fi = *fi;
#  if OPERATION_LOGGING == OPLOG_FULL
  o->f = f;
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
#  if CM == CM_MERGE
#   ifdef MERGE_JIT
  memcpy(o->policy, policy, sizeof(o->policy));
#   else
  o->policy[0] = policy[0];
#   endif /* MERGE_JIT */
  o->delayed = delayed;
#   ifdef MERGE_FEEDBACK
  assert(id.idx < sizeof(tx->feedback) / sizeof(*tx->feedback));
  o->enabled = 1;
  o->executions = 0;
  o->repairs_attempted = 0;
  o->repairs_ok = 0;
  o->aborted_tx = 0;
  o->committed_tx = 0;
#   endif /* MERGE_FEEDBACK */
#  endif /* CM == CM_MERGE */
# endif /* OPERATION_LOGGING != OPLOG_NONE */
  return id;
}

_CALLCONV int
stm_begin_op(const stm_op_id_t op, const stm_merge_cb_t jit, ...)
{
  int r = 0;
#if OPERATION_LOGGING != OPLOG_NONE
  TX_GET;
  va_list args;
  va_start(args, jit);
  r = int_stm_begin_op(tx, op, jit, args);
  va_end(args);
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  return r;
}

_CALLCONV int
stm_end_op(const stm_op_id_t op, const void *ret)
{
  int r = 0;
#if OPERATION_LOGGING != OPLOG_NONE
  TX_GET;
  r = int_stm_end_op(tx, op, ret);
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  return r;
}

_CALLCONV int
stm_finish_merge()
{
#if CM == CM_MERGE
  TX_GET;
  if (likely(tx->merge)) {
    int_stm_resume(tx);

    tx->merge->result = STM_MERGE_OK_USER;
# ifdef NDEBUG
    int_stm_merge_finish(tx, tx->merge
# if OPERATION_LOGGING != OPLOG_NONE
      , GET_LOG_ENTRY(tx, tx->merge->context.current.idx)
# endif /* OPERATION_LOGGING != OPLOG_NONE */
    );
# else
    const int recurse = int_stm_merge_finish(tx, tx->merge
# if OPERATION_LOGGING != OPLOG_NONE
      , GET_LOG_ENTRY(tx, tx->merge->context.current.idx)
# endif /* OPERATION_LOGGING != OPLOG_NONE */
    );
    assert(!recurse);
# endif /* NDEBUG */
  }
  return 1;
#endif /* CM == CM_MERGE */
  return 0;
}

_CALLCONV ALIGNED const stm_read_t
stm_did_load(const stm_word_t *addr)
{
#if CM == CM_MERGE
  TX_GET;
  const r_entry_t *r;
# ifdef READ_SET_SOURCE
  /* Direct lookup for a read from memory */
  r = int_stm_did_load(tx, addr
# if OPERATION_LOGGING == OPLOG_FULL
    , int_stm_get_log(tx)
# endif /* OPERATION_LOGGING == OPLOG_FULL */
    , STM_INVALID_WRITE);
  if (!r) {
    /* Otherwise, search through the ordered list of reads */
    r = int_stm_did_load2(tx, addr, int_stm_get_log(tx));
  }
# else
  r = int_stm_did_load(tx, addr
#  if OPERATION_LOGGING == OPLOG_FULL
    , int_stm_get_log(tx)
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
  );
# endif /* READ_SET_SOURCE */
  return r ? READ_FROM_POINTER(tx, r) : STM_INVALID_READ;
#endif /* CM == CM_MERGE */
  return STM_INVALID_READ;
}

_CALLCONV ALIGNED const stm_write_t
stm_did_store(stm_word_t *addr)
{
#if CM == CM_MERGE
  TX_GET;
  const w_entry_unique_t *wu = int_stm_did_store_unique(tx, addr);
  if (wu) {
    const w_entry_t *w = stm_has_written_current(tx, wu
# if OPERATION_LOGGING == OPLOG_FULL
      , int_stm_get_log(tx)
# endif /* OPERATION_LOGGING == OPLOG_FULL */
    );
    return w ? WRITE_FROM_POINTER(tx, w) : STM_INVALID_WRITE;
  }
#endif /* CM == CM_MERGE */
  return STM_INVALID_WRITE;
}

_CALLCONV int stm_load_value(const stm_read_t rt, stm_word_t *value)
{
#if CM == CM_MERGE
  TX_GET;
  assert(value && READ_VALID(tx, rt));
  const r_entry_t *r = POINTER_FROM_READ(tx, rt);
  assert(r->lock);
  *value = r->value;
  return 1;
#endif /* CM == CM_MERGE */
  return 0;
}

_CALLCONV int stm_store_value(const stm_write_t wt, stm_word_t *value)
{
#if CM == CM_MERGE
  TX_GET;
  assert(value && WRITE_VALID(tx, wt));
  const w_entry_t *w = POINTER_FROM_WRITE(tx, wt);
  assert(w->mask);
# if OPERATION_LOGGING == OPLOG_FULL
  assert(OP_VALID(tx, w->op));
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  if ((w->mask == ~(stm_word_t)0)) {
    *value = w->value;
    return 1;
  }
#endif /* CM == CM_MERGE */
  return 0;
}

_CALLCONV int
stm_load_update(const stm_read_t rt, stm_word_t *value)
{
#if CM == CM_MERGE
  TX_GET;
  assert(READ_VALID(tx, rt));
  r_entry_t *r = POINTER_FROM_READ(tx, rt);
  assert(r->lock);
  *value = int_stm_load_update(tx, r);
  return 1;
#endif /* CM == CM_MERGE */
  return 0;
}

_CALLCONV int
stm_undo_load(const stm_read_t rt)
{
  TX_GET;
  return stm_undo_load_tx(tx, rt);
}

_CALLCONV int
stm_undo_load_tx(stm_tx_t *tx, const stm_read_t rt)
{
#if CM == CM_MERGE
  assert(READ_VALID(tx, rt));
  assert(tx->merge);
  r_entry_t *r = POINTER_FROM_READ(tx, rt);
  assert(STM_SAME_OP(tx->merge->context.current, r->op));
  int_stm_undo_load(tx, r, 1, 1);
  return 1;
#endif /* CM == CM_MERGE */
  return 0;
}

_CALLCONV ALIGNED int
stm_store_update(const stm_write_t wt, const stm_word_t v)
{
#if CM == CM_MERGE
  TX_GET;
  assert(WRITE_VALID(tx, wt));
  w_entry_t *w = POINTER_FROM_WRITE(tx, wt);
  assert(w->mask);
# if OPERATION_LOGGING == OPLOG_FULL
  assert(OP_VALID(tx, w->op));
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  return int_stm_store_update(tx, w, v, ~(stm_word_t)0);
#endif /* CM == CM_MERGE */
  return 0;
}

_CALLCONV ALIGNED int
stm_store2_update(const stm_write_t wt, const stm_word_t v, const stm_word_t mask)
{
#if CM == CM_MERGE
  TX_GET;
  assert(WRITE_VALID(tx, wt));
  w_entry_t *w = POINTER_FROM_WRITE(tx, wt);
  assert(w->mask);
# if OPERATION_LOGGING == OPLOG_FULL
  assert(OP_VALID(tx, w->op));
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  return int_stm_store_update(tx, w, v, mask);
#endif /* CM == CM_MERGE */
  return 0;
}

_CALLCONV int
stm_undo_store(const stm_write_t wt)
{
  TX_GET;
  return stm_undo_store_tx(tx, wt);
}

_CALLCONV int
stm_undo_store_tx(stm_tx_t *tx, const stm_write_t wt)
{
#if CM == CM_MERGE
  assert(WRITE_VALID(tx, wt));
  w_entry_t *w = POINTER_FROM_WRITE(tx, wt);
#if OPERATION_LOGGING == OPLOG_FULL
  assert(STM_SAME_OP(tx->merge->context.current, w->op));
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  int_stm_undo_store(tx, w);
  return 1;
#endif /* CM == CM_MERGE */
  return 0;
}

_CALLCONV uintptr_t
stm_get_load_tag(const stm_read_t rt)
{
#ifdef READ_SET_TAGGED
  TX_GET;
  assert(READ_VALID(tx, rt));
  const r_entry_t *r = POINTER_FROM_READ(tx, rt);
  assert(r->lock);
  return r->tag;
#endif /* READ_SET_TAGGED */
  return 0;
}

_CALLCONV int
stm_set_load_tag(const stm_read_t rt, const uintptr_t tag)
{
#ifdef READ_SET_TAGGED
  TX_GET;
  assert(READ_VALID(tx, rt));
  r_entry_t *r = POINTER_FROM_READ(tx, rt);
  assert(r->lock);
  r->tag = tag;
  return 1;
#endif /* READ_SET_TAGGED */
  return 0;
}

_CALLCONV const stm_op_id_t
stm_get_op_opcode(stm_op_t o)
{
  stm_op_id_t id = STM_INVALID_OPID;
#if OPERATION_LOGGING != OPLOG_NONE
  TX_GET;
  assert(OP_VALID(tx, o));
  const op_entry_t *e = GET_LOG_ENTRY(tx, o.idx);
  assert(OPID_VALID(e->id));
# if OPERATION_LOGGING == OPLOG_FULL
  assert(e->status != OP_STATUS_REVERTED);
# endif /* OPERATION_LOGGING == OPLOG_FULL */
  id.idx = e->id.idx;
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  return id;
}

_CALLCONV const stm_op_id_t
stm_get_load_opcode(const stm_read_t rt)
{
  stm_op_id_t id = STM_INVALID_OPID;
#if OPERATION_LOGGING != OPLOG_NONE
  TX_GET;
  assert(READ_VALID(tx, rt));
  const r_entry_t *r = POINTER_FROM_READ(tx, rt);
  assert(r->lock);
  id.idx = GET_LOG_ENTRY(tx, r->op.idx)->id.idx;
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  return id;
}

_CALLCONV const stm_op_id_t
stm_get_store_opcode(const stm_write_t wt)
{
  stm_op_id_t id = STM_INVALID_OPID;
#if OPERATION_LOGGING == OPLOG_FULL
  TX_GET;
  assert(WRITE_VALID(tx, wt));
  const w_entry_t *w = POINTER_FROM_WRITE(tx, wt);
  assert(w->mask && OP_VALID(tx, w->op));
  id.idx = GET_LOG_ENTRY(tx, w->op.idx)->id.idx;
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  return id;
}

_CALLCONV const stm_word_t *
stm_get_load_addr(const stm_read_t rt)
{
#if CM == CM_MERGE
  TX_GET;
  assert(READ_VALID(tx, rt));
  const r_entry_t *r = POINTER_FROM_READ(tx, rt);
  assert(r->lock);
  return r->addr;
#endif /* CM == CM_MERGE */
  return NULL;
}

_CALLCONV const stm_word_t *
stm_get_store_addr(const stm_write_t wt)
{
  TX_GET;
  assert(WRITE_VALID(tx, wt));
  const w_entry_t *w = POINTER_FROM_WRITE(tx, wt);
  assert(w->mask);
#if OPERATION_LOGGING == OPLOG_FULL
  assert(OP_VALID(tx, w->op));
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  return POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->addr;
}

_CALLCONV const stm_op_t
stm_get_current_op()
{
  stm_op_t o = STM_INVALID_OP;
#if OPERATION_LOGGING != OPLOG_NONE
  TX_GET;
  o.idx = tx->op_current.idx;
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  return o;
}

_CALLCONV const stm_op_t
stm_get_load_op(const stm_read_t rt)
{
  stm_op_t o = STM_INVALID_OP;
#if OPERATION_LOGGING != OPLOG_NONE
  TX_GET;
  assert(READ_VALID(tx, rt));
  const r_entry_t *r = POINTER_FROM_READ(tx, rt);
  assert(r->lock);
  o.idx = r->op.idx;
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  return o;
}

_CALLCONV const stm_op_t
stm_get_store_op(const stm_write_t wt)
{
  stm_op_t o = STM_INVALID_OP;
#if OPERATION_LOGGING == OPLOG_FULL
  TX_GET;
  assert(WRITE_VALID(tx, wt));
  const w_entry_t *w = POINTER_FROM_WRITE(tx, wt);
  assert(w->mask && OP_VALID(tx, w->op));
  o.idx = w->op.idx;
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  return o;
}

_CALLCONV const stm_write_t
stm_get_load_source(const stm_read_t rt)
{
#ifdef READ_SET_SOURCE
  TX_GET;
  assert(READ_VALID(tx, rt));
  const r_entry_t *r = POINTER_FROM_READ(tx, rt);
  return r->source;
#endif /* READ_SET_SOURCE */
  return STM_INVALID_WRITE;
}

_CALLCONV const stm_read_t
stm_get_load_next(const stm_read_t rt, const int op, const int addr)
{
#if OPERATION_LOGGING == OPLOG_FULL
  TX_GET;
  assert(READ_VALID(tx, rt));
  return int_stm_load_next(tx, rt, op, addr);
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  return STM_INVALID_READ;
}

_CALLCONV const stm_write_t
stm_get_store_next(const stm_write_t wt, const int addr)
{
#if OPERATION_LOGGING == OPLOG_FULL
  TX_GET;
  assert(WRITE_VALID(tx, wt));
  if (!addr) {
    // FIXME: Write set is not ordered
    stm_write_t next = { .idx = wt.idx + 1 };
    if (WRITE_VALID_FAST(tx, next))
      return next;
  }
# if OPERATION_LOGGING == OPLOG_FULL
  return int_stm_store_next(tx, POINTER_FROM_WRITE(tx, wt));
# endif /* OPERATION_LOGGING == OPLOG_FULL */
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  return STM_INVALID_WRITE;
}

_CALLCONV const stm_read_t
stm_get_load_last(const stm_read_t rt)
{
#if OPERATION_LOGGING == OPLOG_FULL
  TX_GET;
  assert(READ_VALID(tx, rt));
  return int_stm_load_last(tx, rt);
#endif /* OPERATION_LOGGING */
  return STM_INVALID_READ;
}

_CALLCONV ssize_t
stm_get_op_args(const stm_op_t o, const stm_union_t *args[])
{
#if OPERATION_LOGGING == OPLOG_FULL
  TX_GET;
  assert(OP_VALID(tx, o));
  const op_entry_t *e = GET_LOG_ENTRY(tx, o.idx);
  assert(OPID_VALID(e->id));
  assert(e->status != OP_STATUS_REVERTED);
# if CM == CM_MERGE
  assert(STM_SAME_OP(tx->merge->context.current, o) || OP_SUBTREE(tx->merge->context.current.idx, o));
  if (STM_SAME_OP(tx->merge->context.current, o) || OP_SUBTREE(tx->merge->context.current.idx, o))
# else
  if (1)
# endif /* CM == CM_MERGE */
  {
    *args = e->args;
    return _tinystm.op_info.ids[e->id.idx].fi.nargs;
  }
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  return -1;
}

_CALLCONV unsigned short
stm_get_op_ret(const stm_op_t o, stm_union_t *ret)
{
#if OPERATION_LOGGING == OPLOG_FULL
  TX_GET;
  assert(OP_VALID(tx, o));
  op_entry_t *e = GET_LOG_ENTRY(tx, o.idx);
  assert(OPID_VALID(e->id));
  assert(e->status != OP_STATUS_REVERTED);
# if CM == CM_MERGE
  assert(STM_SAME_OP(tx->merge->context.current, o) || OP_SUBTREE(tx->merge->context.current.idx, o));
  if (STM_SAME_OP(tx->merge->context.current, o) || OP_SUBTREE(tx->merge->context.current.idx, o))
# else
  if (1)
# endif /* CM == CM_MERGE */
  {
    if (_tinystm.op_info.ids[e->id.idx].fi.rtype->type == FFI_TYPE_STRUCT)
      ret->ptr = &e->args[_tinystm.op_info.ids[e->id.idx].fi.nargs];
    else if (_tinystm.op_info.ids[e->id.idx].fi.rtype->type != FFI_TYPE_VOID)
      *ret = e->args[_tinystm.op_info.ids[e->id.idx].fi.nargs];
    return _tinystm.op_info.ids[e->id.idx].fi.rtype->type;
  }
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  return 0;
}

_CALLCONV int
stm_clear_op(const stm_op_t o, int read, int write, int mem)
{
#if CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL)
  TX_GET;
  assert(OP_VALID(tx, o));
  op_entry_t *e = GET_LOG_ENTRY(tx, o.idx);
  if (e->status != OP_STATUS_REVERTED) {
    if (write)
      int_stm_clear_write(tx, o);
    if (read)
      int_stm_clear_read(tx, o, e);
    if (mem)
      stm_undo_mem_op(o);
    return 1;
  }
#endif /* CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL) */
  return 0;
}

_CALLCONV int
stm_undo_op(const stm_op_t o)
{
#if CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL)
  TX_GET;
  assert(OP_VALID(tx, o));
  return int_stm_iterate_op(tx, o, STM_INVALID_OPID, int_stm_undo_op);
#endif /* CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL) */
  return 0;
}

_CALLCONV int
stm_undo_op_descendants(const stm_op_t o, const stm_op_id_t arg)
{
#if CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL)
  TX_GET;
  assert(OP_VALID(tx, o) && OPID_VALID(arg));
  return int_stm_iterate_op(tx, o, arg, int_stm_undo_op_descendants);
#endif /* CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL) */
  return 0;
}

_CALLCONV const stm_op_t
stm_find_op_descendant(const stm_op_t o, const stm_op_id_t arg)
{
  stm_op_t rv = STM_INVALID_OP;
#if CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL)
  TX_GET;
  assert(OP_VALID(tx, o) && OPID_VALID(arg));
  rv.idx = o.idx + int_stm_iterate_op(tx, o, arg, int_stm_find_op_descendant);
  if (!OP_VALID(tx, rv))
    rv = STM_INVALID_OP;
#endif /* CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL) */
  return rv;
}

/* ################################################################### *
 * UNDOCUMENTED STM FUNCTIONS (USE WITH CARE!)
 * ################################################################### */

#ifdef CONFLICT_TRACKING
/*
 * Get thread identifier of other transaction.
 */
_CALLCONV int
stm_get_thread_id(const stm_tx_t *tx, pthread_t *id)
{
  *id = tx->thread_id;
  return 1;
}
#endif /* CONFLICT_TRACKING */

/*
 * Set the CURRENT transaction as irrevocable.
 */
static INLINE int
int_stm_set_irrevocable(stm_tx_t *tx, int serial)
{
#ifdef IRREVOCABLE_ENABLED
  stm_word_t t;

  if (!IS_ACTIVE(tx->status) && serial != -1) {
    /* Request irrevocability outside of a transaction or in abort handler (for next execution) */
    tx->irrevocable = 1 + (serial ? 0x08 : 0);
    return 0;
  }

  /* Are we already in irrevocable mode? */
  if ((tx->irrevocable & 0x07) == 3) {
    return 1;
  }

  if (tx->irrevocable == 0) {
    /* Acquire irrevocability for the first time */
    tx->irrevocable = 1 + (serial ? 0x08 : 0);
    /* Try acquiring global lock */
    t = 0;
    if (_tinystm.irrevocable == 1 || ATOMIC_CAS_FULL(&_tinystm.irrevocable, t, 1) == 0) {
      /* Transaction will acquire irrevocability after rollback */
      stm_rollback(tx, STM_ABORT_IRREVOCABLE);
      return 0;
    }
    /* Success: remember we have the lock */
    tx->irrevocable++;
    /* Try validating transaction */
#if DESIGN == WRITE_BACK_ETL || DESIGN == WRITE_BACK_ETL_VR
    if (!stm_wbetl_validate(tx)) {
      stm_rollback(tx, STM_ABORT_VAL_COMMIT);
      return 0;
    }
#elif DESIGN == WRITE_BACK_CTL
    if (!stm_wbctl_validate(tx)) {
      stm_rollback(tx, STM_ABORT_VAL_COMMIT);
      return 0;
    }
#elif DESIGN == WRITE_THROUGH
    if (!stm_wt_validate(tx)) {
      stm_rollback(tx, STM_ABORT_VAL_COMMIT);
      return 0;
    }
#elif DESIGN == MODULAR
    if ((tx->attr.id == WRITE_BACK_CTL && !stm_wbctl_validate(tx))
       || (tx->attr.id == WRITE_THROUGH && !stm_wt_validate(tx))
       || ((tx->attr.id == WRITE_BACK_ETL || tx->attr.id == WRITE_BACK_ETL_VR) && !stm_wbetl_validate(tx))) {
      stm_rollback(tx, STM_ABORT_VAL_COMMIT);
      return 0;
    }
#endif /* DESIGN == MODULAR */

# ifdef TRANSACTION_OPERATIONS
   /* We might still abort if we cannot set status (e.g., we are being killed) */
    t = tx->status;
    if (GET_STATUS(t) != TX_ACTIVE_BIT || UPDATE_STATUS(tx->status, t, t + (TX_IRREVOCABLE - TX_ACTIVE_BIT)) == 0) {
      stm_rollback(tx, STM_ABORT_KILLED);
      return 0;
    }
# endif /* TRANSACTION_OPERATIONS */
    if (serial && tx->w_set.nb_entries != 0) {
      /* TODO: or commit the transaction when we have the irrevocability. */
      /* Don't mix transactional and direct accesses => restart with direct accesses */
      stm_rollback(tx, STM_ABORT_IRREVOCABLE);
      return 0;
    }
  } else if ((tx->irrevocable & 0x07) == 1) {
    t = 0;
    /* Acquire irrevocability after restart (no need to validate) */
    while (_tinystm.irrevocable == 1 || ATOMIC_CAS_FULL(&_tinystm.irrevocable, t, 1) == 0)
      ;
    /* Success: remember we have the lock */
    tx->irrevocable++;
  }
  assert((tx->irrevocable & 0x07) == 2);

  /* Are we in serial irrevocable mode? */
  if ((tx->irrevocable & 0x08) != 0) {
    /* Stop all other threads */
    if (stm_quiesce(tx, 1) != 0) {
      /* Another thread is quiescing and we are active (trying to acquire irrevocability) */
      assert(serial != -1);
      stm_rollback(tx, STM_ABORT_IRREVOCABLE);
      return 0;
    }
  }

  /* We are in irrevocable mode */
  tx->irrevocable++;

#else /* ! IRREVOCABLE_ENABLED */
  fprintf(stderr, "Irrevocability is not supported in this configuration\n");
  exit(-1);
#endif /* ! IRREVOCABLE_ENABLED */
  return 1;
}

_CALLCONV NOINLINE int
stm_set_irrevocable(int serial)
{
  TX_GET;
  return int_stm_set_irrevocable(tx, serial);
}

_CALLCONV NOINLINE int
stm_set_irrevocable_tx(stm_tx_t *tx, int serial)
{
  return int_stm_set_irrevocable(tx, serial);
}

/*
 * Increment the value of global clock (Only for TinySTM developers).
 */
#if DETECTION == TIME_BASED
void
stm_inc_clock(void)
{
  FETCH_INC_CLOCK;
}
#endif /* DETECTION == TIME_BASED */
