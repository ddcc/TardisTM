/*
 * File:
 *   stm_wbctl.h
 * Author(s):
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * Description:
 *   STM internal functions for write-back CTL.
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

#ifndef _STM_WBCTL_H_
#define _STM_WBCTL_H_

static INLINE int
stm_wbctl_validate(stm_tx_t *tx)
{
  r_entry_t *r;
#ifdef READ_SET_SOURCE
  w_entry_t *w;
#endif /* READ_SET_SOURCE */
  const w_entry_unique_t *wu = NULL;
  stm_version_t contents;
#if DETECTION == TIME_BASED
  stm_version_t l;
#endif /* DETECTION == TIME_BASED */
  tx_conflict_t conflict;
  stm_tx_policy_t decision;
  stm_read_t rt;

  PRINT_DEBUG("==> stm_wbctl_validate(%p[%lu])\n", tx, (unsigned long)tx->end);

  /* Validate reads */
begin:
  rt.idx =
#if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
    READ_RESERVED_IDX + 1
#else
    0
#endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
  ;

#ifdef READ_SET_ORDERED
  if (tx->attr.read_set_ordered)
    rt = tx->r_set.head;
#endif /* READ_SET_ORDERED */

  /* Validate reads */
  for (; likely(READ_VALID_FAST(tx, rt));
    rt =
# ifdef READ_SET_ORDERED
    tx->attr.read_set_ordered ? r->next :
# endif /* READ_SET_ORDERED */
    READ_FROM_POINTER(tx, r + 1)
  ) {

    r = POINTER_FROM_READ(tx, rt);
    assert(READ_POINTER_VALID(tx, r));

#if CM == CM_MERGE && defined(READ_SET_ORDERED)
  if (tx->attr.read_set_ordered)
    assert(r->lock);
  else if (!r->lock)
    continue;
#elif DETECTION == TIME_BASED
  if (!r->lock)
    continue;
#endif /* CM == CM_MERGE && READ_SET_ORDERED */
 restart:
#ifdef READ_SET_SOURCE
    /* Source is from the write set, so just compare directly */
    if (WRITE_VALID_FAST(tx, r->source)) {
      w = POINTER_FROM_WRITE(tx, r->source);
      if (w->version == r->version)
        continue;
      goto conflict;
    } else
      w = NULL;
    assert(!w || r->addr == POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->addr);
#endif /* READ_SET_SOURCE */

    /* Check against memory only if it is the source of the read, or if the write-set entry is partial due to masking */
#if DETECTION == TIME_BASED
    /* Read lock */
    l = LOCK_READ(r->lock);
restart_no_load:
#endif /* DETECTION == TIME_BASED */

#if DETECTION == TIME_BASED
    /* Unlocked and still the same version? */
    if (LOCK_GET_OWNED(r->addr, l)) {
      /* Do we own the lock? */
      wu = (w_entry_unique_t *)LOCK_GET_ADDR(l);
      /* Check if address falls inside our write set (avoids non-faulting load) */
      if (!WRITE_UNIQUE_POINTER_VALID(tx, wu))
      {
        /* Locked by another transaction: cannot validate */
        conflict.entries.type = STM_RW_CONFLICT;
        conflict.entries.e1 = ENTRY_FROM_READ_POINTER(tx, r);
        conflict.entries.e2 = ENTRY_FROM_WRITE(tx, wu->latest);
# ifdef CONFLICT_TRACKING
        conflict.other = wu->tx;
        conflict.status = wu->tx->status;
# endif /* CONFLICT_TRACKING */
# ifdef CONTENDED_LOCK_TRACKING
        conflict.lock = r->lock;
# endif /* CONTENDED_LOCK_TRACKING */
        decision = stm_conflict_handle(tx, &conflict);
        goto handle;
      }
    } else
      wu = NULL;
#endif /* DETECTION == TIME_BASED */

    /* We own the lock, or it is unlocked */
#if DETECTION == TIME_BASED
    contents = wu ? wu->version : LOCK_GET_TIMESTAMP(l);
#endif /* DETECTION */

check:
#if DETECTION == TIME_BASED
    if (contents == r->version) {
      /* Time-based: Version matches */
      continue;
    }
#endif /* DETECTION */

conflict:
    /* Validation failed */
    conflict.entries.type = STM_RD_VALIDATE;
    conflict.entries.e1 = ENTRY_FROM_READ_POINTER(tx, r);
#if DETECTION == TIME_BASED && !defined(READ_SET_SOURCE)
    conflict.entries.e2 = wu ? ENTRY_FROM_WRITE(tx, wu->latest) : ENTRY_INVALID;
#elif defined(READ_SET_SOURCE)
    conflict.entries.e2 = w ? ENTRY_FROM_WRITE_POINTER(tx, w) : ENTRY_INVALID;
#else
    conflict.entries.e2 = ENTRY_INVALID;
#endif
#ifdef CONFLICT_TRACKING
    conflict.other = tx;
    conflict.status = tx->status;
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
    conflict.lock = NULL;
#endif /* CONTENDED_LOCK_TRACKING */

    decision = stm_conflict_handle(tx, &conflict);
handle:
    switch (decision) {
      case STM_RETRY:
      case STM_SKIP:
#if !defined(MERGE_UNLOCK) && (CM == CM_MERGE || defined(MERGE_LOCK_CONFLICT)) && (DETECTION == TIME_BASED)
        if (tx->revalidate)
          return -1;
#endif /* !MERGE_UNLOCK && (CM == CM_MERGE || MERGE_LOCK_CONFLICT) && (DETECTION == TIME_BASED) */

#if CM == CM_MERGE
# if OPERATION_LOGGING != OPLOG_NONE
        /* Read set may have expanded, so obtain the current pointer */
        r = POINTER_FROM_READ(tx, rt);
        assert(READ_POINTER_VALID(tx, r));
        if (unlikely(!r->lock)) {
          /* Merge may have reverted the current read, or altered other reads/writes in the current operation. Thus, must restart from the beginning of the operation. */
#  if OPERATION_LOGGING == OPLOG_FULL
          if (OP_VALID(tx, r->op)) {
            op_entry_t *e = GET_LOG_ENTRY(tx, r->op.idx);
            if (READ_VALID_FAST(tx, e->reads)) {
              rt = e->reads;
              r = POINTER_FROM_READ(tx, rt);
              goto restart;
            }
          }
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
          goto begin;
        }
# endif /* OPERATION_LOGGING != OPLOG_NONE */
#endif /* CM == CM_MERGE */

        if (decision == STM_RETRY) {
          /* Restart at the current read */
          goto restart;
        }
        continue;
      break;
      default:
        assert(decision == STM_KILL_SELF);
        return 0;
      break;
    }
  }

  return 1;
}

/*
 * Extend snapshot range.
 */
static INLINE int
stm_wbctl_extend(stm_tx_t *tx
#if DETECTION == TIME_BASED
  , stm_version_t l
#endif /* DETECTION == TIME_BASED */
  ) {
  PRINT_DEBUG("==> stm_wbctl_extend(%p[%lu])\n", tx, (unsigned long)tx->end);

  assert(IS_ACTIVE(tx->status));

#ifdef UNIT_TX
  /* Extension is disabled */
  if (tx->attr.no_extend)
    return 0;
#endif /* UNIT_TX */

#  ifdef TM_STATISTICS
  ++tx->stat_extensions;
#  endif /* TM_STATISTICS */

#if DETECTION == TIME_BASED
  /* No need to check clock overflow here. The clock can exceed up to MAX_THREADS and it will be reset when the quiescence is reached. */
# if CM == CM_MERGE
  tx->end_next = l;
# endif /* CM == CM_MERGE */
#endif /* DETECTION */

  /* Try to validate read set */
  int ret = stm_wbctl_validate(tx);
  if (ret == 1) {
#if DETECTION == TIME_BASED
    /* It works: we can extend until now */
    tx->end = l;
#endif /* DETECTION */
    return ret;
  }

  return ret;
}

#if DETECTION == TIME_BASED
static INLINE int
stm_wbctl_lock(stm_tx_t *tx, w_entry_unique_t *wu
#ifndef MERGE_UNLOCK
  , int swap
#endif /* MERGE_UNLOCK */
) {
  stm_version_t l;

  /* Acquire locks on write set */
  assert(WRITE_UNIQUE_POINTER_VALID(tx, wu));
  assert(wu->lock);
  /* Try to acquire lock */
restart:
  l = LOCK_READ(wu->lock);
  if (LOCK_GET_OWNED(wu->addr, l)) {
    /* Do we already own the lock? */
    w_entry_unique_t *wu2 = (w_entry_unique_t *)LOCK_GET_ADDR(l);
    if (WRITE_UNIQUE_POINTER_VALID(tx, wu2)) {
      assert(wu->lock == wu2->lock && !wu2->no_drop);
      assert(wu == wu2 || wu->no_drop);
#ifndef MERGE_UNLOCK
      /* Swap the lock if this is a new write */
      if (swap && wu != wu2 && wu->no_drop) {
        wu->no_drop = 0;
        wu->version = wu2->version;
        wu2->no_drop = 1;
        wu2->version = 0;
swap:
        if (unlikely(!LOCK_WRITE_CAS(wu->lock, l, LOCK_SET_ADDR_WRITE(wu, l)))) {
          l = LOCK_READ(wu->lock);
          goto swap;
        }
      }
#endif /* !MERGE_UNLOCK */
      /* Yes: ignore */
      return 2;
    }
    /* Conflict: CM kicks in */
#ifdef IRREVOCABLE_ENABLED
    if (tx->irrevocable) {
# ifdef IRREVOCABLE_IMPROVED
      if (ATOMIC_LOAD(&_tinystm.irrevocable) == 1)
        ATOMIC_STORE(&_tinystm.irrevocable, 2);
# endif /* IRREVOCABLE_IMPROVED */
      /* Spin while locked */
      goto restart;
    }
#endif /* IRREVOCABLE_ENABLED */

    tx_conflict_t conflict = {
      .entries.type = STM_WW_CONFLICT,
      .entries.e1 = ENTRY_FROM_WRITE(tx, wu->latest),
      .entries.e2 = ENTRY_FROM_WRITE(tx, wu2->latest),
#ifdef CONFLICT_TRACKING
      .other = wu2->tx,
      .status = wu2->tx->status,
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
      .lock = wu->lock,
#endif /* CONTENDED_LOCK_TRACKING */
    };

    stm_tx_policy_t decision = stm_conflict_handle_all(tx, &conflict);
    switch (decision) {
      case STM_RETRY:
        return 0;
      break;
      case STM_SKIP:
        return 1;
      break;
      default:
        assert(decision == STM_KILL_SELF);
        stm_rollback(tx, STM_ABORT_WW_CONFLICT);
        return 0;
      break;
    }
  }

  if (unlikely(LOCK_WRITE_CAS(wu->lock, l, LOCK_SET_ADDR_WRITE(wu, l)) == 0))
    goto restart;
  assert(LOCK_GET_OWNED(wu->addr, LOCK_READ(wu->lock)));
  /* We own the lock here */
  wu->no_drop = 0;
# if DETECTION == TIME_BASED
  /* Store version for validation of read set */
  wu->version = LOCK_GET_TIMESTAMP(l);
# endif /* DETECTION == TIME_BASED */
  assert(tx->w_set_unique.nb_entries >= tx->w_set_unique.nb_acquired);
  tx->w_set_unique.nb_acquired++;
  return 1;
}

static INLINE int
stm_wbctl_lock_all(stm_tx_t *tx) {
  /* Acquire locks (in reverse order) */
  for (w_entry_unique_t *wu = tx->w_set_unique.entries + tx->w_set_unique.nb_entries - 1; likely(WRITE_UNIQUE_POINTER_VALID(tx, wu)); --wu) {
    /* With locking while merging, must grab all locks to avoid write-write conflicts and maintain two-phase locking */
    if (!stm_wbctl_lock(tx, wu
#ifndef MERGE_UNLOCK
      , 0
#endif /* !MERGE_UNLOCK */
    ))
      return 0;
  }

  return 1;
}
#endif /* DETECTION == TIME_BASED */

static INLINE void
stm_wbctl_rollback(stm_tx_t *tx) {
  PRINT_DEBUG("==> stm_wbctl_rollback(%p[%lu])\n", tx, (unsigned long)tx->end);

  assert(IS_ACTIVE(tx->status));
  assert(tx->w_set_unique.nb_entries >= tx->w_set_unique.nb_acquired);

#if DETECTION == TIME_BASED
  for (w_entry_unique_t *wu = tx->w_set_unique.entries + tx->w_set_unique.nb_entries - 1; likely(tx->w_set_unique.nb_acquired > 0); --wu) {
    assert(WRITE_UNIQUE_POINTER_VALID(tx, wu));
    assert(wu->lock);

    if (!wu->no_drop) {
      assert(tx->w_set_unique.nb_acquired > 0 && tx->w_set_unique.nb_entries >= tx->w_set_unique.nb_acquired);
      assert(LOCK_GET_OWNED(wu->addr, LOCK_READ_ACQ(wu->lock)) && WRITE_UNIQUE_POINTER_VALID(tx, (w_entry_unique_t *)LOCK_GET_ADDR(LOCK_READ_ACQ(wu->lock))) && ((w_entry_unique_t *)(LOCK_GET_ADDR(LOCK_READ_ACQ(wu->lock))))->lock == wu->lock);
      tx->w_set_unique.nb_acquired -= 1;
      if (tx->w_set_unique.nb_acquired == 0) {
        /* Make sure that all lock releases become visible to other threads */
        LOCK_WRITE_REL(wu->lock, LOCK_SET_TIMESTAMP(wu, wu->version, LOCK_READ_ACQ(wu->lock)));
      } else {
        LOCK_WRITE(wu->lock, LOCK_SET_TIMESTAMP(w, wu->version, LOCK_READ(wu->lock)));
      }
      assert(!LOCK_GET_OWNED(wu->addr, LOCK_READ(wu->lock)));
      /* Reset the lock status, in case commit is re-attempted */
      wu->no_drop = 1;
    }
  }
#endif /* DETECTION == TIME_BASED */
}

static INLINE stm_word_t
stm_wbctl_read(stm_tx_t *tx, const stm_word_t *addr
#ifdef READ_SET_TAGGED
  , const uintptr_t tag
#endif /* READ_SET_TAGGED */
) {
  stm_word_t value;
#if DETECTION == TIME_BASED
  const stm_lock_t *lock;
  stm_version_t l, l2, version;
#endif /* DETECTION == TIME_BASED */
  const w_entry_t *w;

  PRINT_DEBUG2("==> stm_wbctl_read(t=%p[%lu],a=%p)\n", tx, (unsigned long)tx->end, addr);

  assert(IS_ACTIVE(tx->status));

read:
  /* Did we previously write the same address? */
  w = stm_has_written(tx, (stm_word_t *)addr);
  assert(!w || w->mask);

  if (w) {
    assert(w->mask);
    if (w->mask == ~(stm_word_t)0) {
      value = w->value;
# ifdef READ_SET_SOURCE
      /* Record a read of the write set */
      lock = POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->lock;
      version = w->version;
      goto add_to_read_set;
# else
      return value;
# endif /* READ_SET_SOURCE */
    }
  }

#if DETECTION == TIME_BASED
  /* Get reference to lock */
  lock = GET_LOCK(addr);

  /* Read lock, value, lock */
restart:
  l = LOCK_READ_ACQ(lock);
restart_no_load:
  if (LOCK_GET_WRITE(addr, l)) {
    w_entry_unique_t *wu2 = (w_entry_unique_t *)LOCK_GET_ADDR(l);
    if (WRITE_UNIQUE_POINTER_VALID(tx, wu2)) {
      if (w) {
        assert(POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->addr == wu2->addr);
        /* Locked by us for this address, read from the pending write */
        value = (w->mask == ~(stm_word_t)0) ? w->value : ((ATOMIC_LOAD_ACQ(addr) & ~w->mask) | (w->value & w->mask));
      } else {
        /* Locked by us for a different address, read from memory */
        value = ATOMIC_LOAD_ACQ(addr);
      }
# if DETECTION == TIME_BASED
      version = wu2->version;
# endif /* DETECTION == TIME_BASED */
      goto add_to_read_set;
    }

#if !defined(MERGE_UNLOCK) && CM == CM_MERGE
    /* Cannot spin while merging and holding locks, because this can lead to deadlock. */
    if (tx->merge && tx->w_set_unique.nb_acquired > 0) {
      tx_conflict_t conflict = {
        .entries.type = STM_RW_CONFLICT,
        .entries.e1 = ENTRY_INVALID,
        .entries.e2 = ENTRY_FROM_WRITE(tx, wu2->latest),
# ifdef CONFLICT_TRACKING
        .other = wu2->tx,
        .status = wu2->tx->status,
# endif /* CONFLICT_TRACKING */
# ifdef CONTENDED_LOCK_TRACKING
        .lock = wu->lock,
# endif /* CONTENDED_LOCK_TRACKING */
      };

      stm_tx_policy_t decision = stm_conflict_handle_all(tx, &conflict);
      switch (decision) {
        case STM_RETRY:
          goto restart;
        break;
        default:
          assert(decision == STM_KILL_SELF);
          return 0;
        break;
      }
    }
#endif /* !MERGE_UNLOCK && CM == CM_MERGE */

    /* Spin while locked (should not last long) */
    goto restart;
  } else {
#endif /* DETECTION == TIME_BASED */
    /* Not locked */
#ifdef IRREVOCABLE_ENABLED
    /* In irrevocable mode, no need check timestamp nor add entry to read set */
    if (tx->irrevocable)
      return ATOMIC_LOAD_ACQ(addr);
#endif /* IRREVOCABLE_ENABLED */
#if DETECTION == TIME_BASED
    /* Check timestamp */
    version = LOCK_GET_TIMESTAMP(l);
    l2 = LOCK_READ_ACQ(lock);
    if (l != l2) {
      l = l2;
      goto restart_no_load;
    }
#endif /* DETECTION == TIME_BASED */

#if DETECTION == TIME_BASED
    /* Valid version? */
    if (
# if CM == CM_MERGE
      (!tx->merge && version > tx->end) || (tx->merge && version > tx->end_next)
# else
      version > tx->end
# endif /* CM == CM_MERGE */
    ) {
      /* No: try to extend first (except for read-only transactions: no read set) */
      if (tx->attr.read_only
# if CM == CM_MERGE
          || tx->merge
# endif /* CM == CM_MERGE */
          || !stm_wbctl_extend(tx, GET_CLOCK)) {
        /* Not much we can do: abort */
        stm_rollback(tx, STM_ABORT_VAL_READ);
        return 0;
      }
# if !defined(MERGE_UNLOCK) && CM == CM_MERGE
      assert(!tx->revalidate || tx->merge);
# endif /* !MERGE_UNLOCK && CM == CM_MERGE */
      /* Restart the read, because there may be a local write */
      goto read;
    }
#endif /* DETECTION == TIME_BASED */
value:
    value = ATOMIC_LOAD_ACQ(addr);
#if DETECTION == TIME_BASED
    /* Verify that version has not been overwritten (read value has not
     * yet been added to read set and may have not been checked during
     * extend) */
    l2 = LOCK_READ_ACQ(lock);
    if (l != l2) {
      l = l2;
      goto restart_no_load;
    }
# if !defined(MERGE_UNLOCK) && CM == CM_MERGE
    assert(!tx->revalidate || tx->merge);
# endif /* !MERGE_UNLOCK && CM == CM_MERGE */
#endif /* DETECTION */
#if DETECTION == TIME_BASED
  }
#endif /* DETECTION == TIME_BASED */
  /* We have a good version: add to read set (update transactions) and return value */

  /* Did we previously write the same address? */
  if (w != NULL) {
    value = (value & ~w->mask) | (w->value & w->mask);
    /* Must still add to read set */
  }
add_to_read_set:
#if (DETECTION == TIME_BASED) && defined(NO_DUPLICATES_IN_RW_SETS)
  r = stm_has_read(tx, addr
# ifdef READ_SET_SOURCE
    , w ? WRITE_FROM_POINTER(tx, w): STM_INVALID_WRITE
# endif /* READ_SET_SOURCE */
  );
  if (r) {
    assert(w || r->value == value);
    return value;
  }
#endif /* (DETECTION == TIME_BASED) && NO_DUPLICATES_IN_RW_SETS */
  stm_add_to_rs(tx, addr
#if DETECTION == TIME_BASED
    , lock, version
#endif /* DETECTION == TIME_BASED */
#if READ_SET_DETAILED
    , value
#endif /* READ_SET_DETAILED */
#ifdef READ_SET_TAGGED
    , tag
#endif /* READ_SET_TAGGED */
#ifdef READ_SET_SOURCE
    , w ? WRITE_FROM_POINTER(tx, w) : STM_INVALID_WRITE
#endif /* READ_SET_SOURCE */
  );
  return value;
}

static INLINE w_entry_t *
stm_wbctl_add_to_ws(stm_tx_t *tx, w_entry_unique_t *wu, stm_word_t *addr, const stm_word_t value, const stm_word_t mask) {
  w_entry_t *w;
  stm_write_t wt;

  assert(mask);
  /* Add address to write set */
  if (unlikely(tx->w_set.nb_entries == tx->w_set.size))
    stm_allocate_ws_entries(tx, 1);
#if WRITE_SET == RW_ADAPTIVE
  else if (!kh_size(tx->w_set.hash) && tx->w_set.nb_entries == RW_ADAPTIVE_THRESHOLD) {
    /* Reached the threshold; add all entries to the hash table */
    for (wt.idx = tx->w_set.nb_entries - 1; likely(wt.idx >= WRITE_RESERVED_IDX + 1); --wt.idx) {
      int ret;
      assert(wt.idx != WRITE_RESERVED_IDX);
      w = POINTER_FROM_WRITE(tx, wt);
      if (
#if CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL)
          !STM_SAME_OP(w->op, STM_SPECIAL_OP)
#else
          1
#endif /* CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL) */
      ) {
        kh_put(w_set, tx->w_set.hash, wt, &ret);
#if CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL)
        assert(ret >= 0);
#else
        assert(ret > 0);
#endif /* CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL) */
      }
    }
  }
#endif /* WRITE_SET == RW_ADAPTIVE */

  w = &tx->w_set.entries[tx->w_set.nb_entries++];
  assert(WRITE_POINTER_VALID(tx, w));
  wt = WRITE_FROM_POINTER(tx, w);
  /* Remember new value */
  w->value = value;
#ifdef READ_SET_SOURCE
  w->version = 0;
#endif /* READ_SET_SOURCE */
  w->mask = mask;
#if OPERATION_LOGGING == OPLOG_FULL
  w->op = int_stm_get_log(tx);
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  w->unique = WRITE_UNIQUE_FROM_POINTER(tx, wu);

#if WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE
  if (
# if WRITE_SET == RW_ADAPTIVE
    kh_size(tx->w_set.hash)
# else
    1
# endif /* WRITE_SET == RW_ADAPTIVE */
  ) {
    int ret;
# if CM == CM_MERGE && (OPERATION_LOGGING == OPLOG_FULL)
    assert(w != &tx->w_set.entries[WRITE_RESERVED_IDX]);
    khiter_t it = kh_put(w_set, tx->w_set.hash, wt, &ret);
    if (!ret) {
      /* Track only the latest write for this operation in the direct lookup */
      assert(!STM_SAME_WRITE(kh_key(tx->w_set.hash, it), wt));
      kh_del(w_set, tx->w_set.hash, it);
      it = kh_put(w_set, tx->w_set.hash, wt, &ret);
    }
# else
    kh_put(w_set, tx->w_set.hash, wt, &ret);
# endif /* CM == CM_MERGE && )OPERATION_LOGGING == OPLOG_FULL) */
    assert(ret > 0);
  }
#endif /* WRITE_SET == RW_HASH_TABLE || WRITE_SET == RW_ADAPTIVE */

#if OPERATION_LOGGING == OPLOG_FULL
  // FIXME: w_set_unique needs to be ordered, otherwise a new write during a merge can be inserted at the end of the w_set_unique list, whereas it may need to take effect before another write (e.g. index into data structure)
# if CM == CM_MERGE
  if (tx->merge) {
    /* Find the position where this write should occur */
    stm_write_t *wtnext = int_stm_store_latest2(tx, &wu->latest, w->op);
    assert(wtnext);

    /* Insert this write */
    w_entry_t *wnext = WRITE_VALID_FAST(tx, *wtnext) ? POINTER_FROM_WRITE(tx, *wtnext) : NULL;
    // FIXME: Allow user to choose sequencing relative to existing reads/writes
    if (wnext && WRITE_VALID_FAST(tx, wnext->addr_prev) && STM_SAME_OP(POINTER_FROM_WRITE(tx, wnext->addr_prev)->op, w->op)) {
      stm_rollback(tx, STM_ABORT_OTHER);
      return NULL;
    }
    w->addr_prev = *wtnext;
    *wtnext = wt;
    assert(WRITE_VALID(tx, wu->latest) || (!WRITE_VALID(tx, wu->latest) && wtnext == &wu->latest));

    /* Set the correct sequence for this write */
    if (tx->merge->policy == STM_MERGE_POLICY_REPLAY) {
      w->op_next.idx = tx->merge->replay.op_log;
    } else {
      op_entry_t *e = GET_LOG_ENTRY(tx, w->op.idx);
      w->op_next.idx = w->op.idx + OP_ENTRY_SIZE(e->id);

      /* Update subsequent reads */
      r_entry_t *r;
      const unsigned int ordered = tx->attr.read_set_ordered;
      for (stm_read_t rt = *int_stm_get_load_position(tx); likely(READ_VALID_FAST(tx, rt)); rt = ordered ? r->next : READ_FROM_POINTER(tx, r + 1)) {
        r = POINTER_FROM_READ(tx, rt);
        if (ordered)
          assert(r->lock);
        else if (!r->lock)
          continue;

        if (r->addr == addr) {
          /* Change the source if it older, and reinsert if necessary */
          if (STM_SAME_WRITE(r->source, STM_INVALID_WRITE) || POINTER_FROM_WRITE(tx, r->source)->op_next.idx <= w->op.idx) {
# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
            if (
#  if READ_SET == RW_ADAPTIVE
              kh_size(tx->r_set.hash)
#  else
              1
#  endif /* READ_SET == RW_ADAPTIVE */
            ) {
              const stm_read_t rt = READ_FROM_POINTER(tx, r);
              khiter_t it = kh_get(r_set, tx->r_set.hash, rt);
              assert(it != kh_end(tx->r_set.hash));
              kh_del(r_set, tx->r_set.hash, it);
            }
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */

            r->source = wt;
            r->version = w->version - 1;

# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
            if (
#  if READ_SET == RW_ADAPTIVE
              kh_size(tx->r_set.hash)
#  else
              1
#  endif /* READ_SET == RW_ADAPTIVE */
            ) {
              int ret;
              assert(r != &tx->r_set.entries[READ_RESERVED_IDX]);
              kh_put(r_set, tx->r_set.hash, rt, &ret);
              assert(ret > 0);
            }
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
          } else
            break;
        }
      }
    }
  } else {
    /* Set the previous pointer to the current latest write */
    w->addr_prev = wu->latest;
    w->op_next.idx = tx->op_log.used;
# endif /* CM == CM_MERGE */
#else
# if CM == CM_MERGE
    assert(!tx->merge || !stm_has_read(tx, addr));
# endif /* CM == CM_MERGE */
#endif /* OPERATION_LOGGING == OPLOG_FULL */
    wu->latest = wt;
#if OPERATION_LOGGING == OPLOG_FULL && CM == CM_MERGE
  }
#endif /* OPERATION_LOGGING == OPLOG_FULL && CM == CM_MERGE */

  return w;
}

static INLINE w_entry_t *
stm_wbctl_write(stm_tx_t *tx, stm_word_t *addr, const stm_word_t value, const stm_word_t mask)
{
#if DETECTION == TIME_BASED
  const stm_lock_t *lock;
  r_entry_t *r;
  stm_version_t l, version;
#endif /* DETECTION == TIME_BASED */
  w_entry_t *w = NULL;
  w_entry_unique_t *wu;

  PRINT_DEBUG2("==> stm_wbctl_write(t=%p[%lu],a=%p,d=%p-%lu,m=0x%lx)\n",
               tx, (unsigned long)tx->end, addr, (void *)value, (unsigned long)value, (unsigned long)mask);

  if (
# if LAZINESS == LZ_ZERO
    1
# elif defined(MERGE_JIT)
    tx->op_mergeable_jit || !tx->op_mergeable_delayed
# else
    !tx->op_mergeable_delayed
# endif /* LAZINESS == LZ_ZERO */
  ) {
# if DETECTION == TIME_BASED
    /* Get reference to lock */
    lock = GET_LOCK(addr);

    /* Try to acquire lock */
   restart:
    l = LOCK_READ_ACQ(lock);
   restart_no_load:
    if (LOCK_GET_OWNED(addr, l)) {
      w_entry_unique_t *wu2 = (w_entry_unique_t *)LOCK_GET_ADDR(l);
      if (!WRITE_UNIQUE_POINTER_VALID(tx, wu2)) {
# if !defined(MERGE_UNLOCK) && CM == CM_MERGE
        /* Cannot spin while merging and committing, because this can lead to deadlock. */
        if (tx->merge && tx->w_set_unique.nb_acquired > 0) {
          tx_conflict_t conflict = {
            .entries.type = STM_RW_CONFLICT,
            .entries.e1 = ENTRY_INVALID,
            .entries.e2 = ENTRY_FROM_WRITE(tx, wu2->latest),
#  ifdef CONFLICT_TRACKING
            .other = wu2->tx,
            .status = wu2->tx->status,
#  endif /* CONFLICT_TRACKING */
#  ifdef CONTENDED_LOCK_TRACKING
            .lock = wu->lock,
#  endif /* CONTENDED_LOCK_TRACKING */
          };

          stm_tx_policy_t decision = stm_conflict_handle_all(tx, &conflict);
          switch (decision) {
            case STM_RETRY:
              goto restart;
            break;
            default:
              assert(decision == STM_KILL_SELF);
              return 0;
            break;
          }
        }
# endif /* !MERGE_UNLOCK && CM == CM_MERGE */

        /* Spin while locked (should not last long) */
        goto restart;
      }

      version = wu2->version;
    } else {
      /* Not locked */
      version = LOCK_GET_TIMESTAMP(l);
    }
# endif /* DETECTION == TIME_BASED */
  }

  if ((wu = int_stm_did_store_unique(tx, addr))) {
    if (mask && (w = stm_has_written_current(tx, wu
# if OPERATION_LOGGING == OPLOG_FULL
      , int_stm_get_log(tx)
# endif /* OPERATION_LOGGING == OPLOG_FULL */
    ))) {
# if OPERATION_LOGGING == OPLOG_FULL
      assert(!OP_VALID(tx, w->op) || GET_OP_IDX(w->op.idx) <= GET_OP_IDX(int_stm_get_log(tx).idx));
# endif /* OPERATION_LOGGING == OPLOG_FULL */

# if OPERATION_LOGGING == OPLOG_FULL
      /* Must check if the previous write is still the latest write to this address. If a sub-operation also wrote to this address, a new straddle write needs to be inserted. */
      if (w->op_next.idx != tx->op_log.used) {
        if (!STM_SAME_WRITE(POINTER_FROM_WRITE_UNIQUE(tx, w->unique)->latest, WRITE_FROM_POINTER(tx, w)))
          return stm_wbctl_add_to_ws(tx, wu, addr, value, mask);
      }
# endif /* OPERATION_LOGGING == OPLOG_FULL */
      w->value = (w->value & ~mask) | (value & mask);
      w->mask |= mask;
      return w;
    }
  } else {
    /* Add address to unique write set */
    wu = stm_add_to_ws_unique(tx, addr);

#if !defined(MERGE_UNLOCK) && (CM == CM_MERGE || defined(MERGE_LOCK_CONFLICT))
    /* Take the lock if committing */
    if (tx->w_set_unique.nb_acquired) {
      assert(GET_STATUS(tx->status) == TX_COMMITTING);
      stm_wbctl_lock(tx, wu, 1);
# if DETECTION == TIME_BASED
      /* Must increment the timestamp due to two-phase locking violation */
      tx->revalidate |= REVALIDATE_CLOCK;
# endif /* DETECTION == TIME_BASED */
    }
#endif /* !MERGE_UNLOCK && (CM == CM_MERGE || MERGE_LOCK_CONFLICT) */
  }


  /* Add write to write set */
  if (mask)
    w = stm_wbctl_add_to_ws(tx, wu, addr, value, mask);

  if (
# if LAZINESS == LZ_ZERO
    1
# elif defined(MERGE_JIT)
    tx->op_mergeable_jit || !tx->op_mergeable_delayed
# else
    !tx->op_mergeable_delayed
# endif /* LAZINESS == LZ_ZERO */
  ) {
    /* Check for revalidation after adding to write set, in case this write needs to be merged */
# if DETECTION == TIME_BASED
    /* Handle write after reads (before CAS) */
#  ifdef IRREVOCABLE_ENABLED
    /* In irrevocable mode, no need to revalidate */
    if (tx->irrevocable)
      return w;
#  endif /* IRREVOCABLE_ENABLED */
    if (version > tx->end) {
      /* We might have read an older version previously from memory */
      if (
#  ifdef UNIT_TX
          tx->attr.no_extend ||
#  endif /* UNIT_TX */
          (r = stm_has_read(tx, addr
#  ifdef READ_SET_SOURCE
            , STM_INVALID_WRITE
#  endif /* READ_SET_SOURCE */
          )) != NULL && r->version < version) {
        /* Read version must be older (otherwise, tx->end >= version) */
        assert(r->version != version);
#  if CM == CM_MERGE
        /* Trigger a full revalidation */
        if (!stm_wbctl_extend(tx, GET_CLOCK)) {
          /* Cannot commit */
          stm_rollback(tx, STM_ABORT_VAL_WRITE);
          return NULL;
        }
#   ifndef MERGE_UNLOCK
       assert(!tx->revalidate || tx->merge);
#   endif /* MERGE_UNLOCK */
#  else
        tx_conflict_t conflict = {
          .entries.type = STM_WR_VALIDATE,
          .entries.e1 = ENTRY_FROM_READ_POINTER(tx, r),
          .entries.e2 = w ? ENTRY_FROM_WRITE_POINTER(tx, w) : ENTRY_INVALID,
#   ifdef CONFLICT_TRACKING
          .other = NULL,
          .status = 0,
#   endif /* CONFLICT_TRACKING */
#   ifdef CONTENDED_LOCK_TRACKING
          .lock = lock,
#   endif /* CONTENDED_LOCK_TRACKING */
        };

        stm_tx_policy_t decision = stm_conflict_handle(tx, &conflict);
        switch (decision) {
          case STM_RETRY:
            goto restart;
          break;
          case STM_SKIP:
          break;
          default:
            assert(decision == STM_KILL_SELF);
            /* Not much we can do: abort */
            stm_rollback(tx, STM_ABORT_VAL_WRITE);
            return NULL;
          break;
        }
#  endif /* CM == CM_MERGE */
        assert(GET_STATUS(tx->status) != TX_COMMITTING);
      }
    }
# endif /* DETECTION == TIME_BASED */
  }

  return w;
}

#if CM == CM_MERGE
static INLINE void
stm_wbctl_write_update(const stm_tx_t *tx, w_entry_t *w, const stm_word_t value, const stm_word_t mask)
{
  PRINT_DEBUG2("==> stm_wbctl_write_update(t=%p[%lu],w=%p,d=%p-%lu,m=0x%lx)\n",
               tx, (unsigned long)tx->end, w, (void *)value, (unsigned long)value, mask);
  assert(tx->merge);
# if OPERATION_LOGGING != OPLOG_NONE
  assert(OP_VALID(tx, tx->merge->context.current));
#  if OPERATION_LOGGING == OPLOG_FULL
  assert(STM_SAME_OP(w->op, int_stm_get_log(tx)));
#  endif /* OPERATION_LOGGING == OPLOG_FULL */
# endif /* OPERATION_LOGGING != OPLOG_NONE */
  assert(WRITE_POINTER_VALID(tx, w));
  assert((w->mask & mask) == mask);
  w->value = (~mask & w->value) | (mask & value);
# if defined(READ_SET_SOURCE) && (DETECTION == TIME_BASED)
  /* Mark that this write set entry has been updated */
  w->version = tx->end_next;
# endif /* READ_SET_SOURCE && (DETECTION == TIME_BASED) */
}

static INLINE stm_word_t
stm_wbctl_read_update(stm_tx_t *tx, r_entry_t *r)
{
  PRINT_DEBUG2("==> stm_wbctl_read_update(t=%p[%lu],a=%p)\n", tx, (unsigned long)tx->end, r->addr);
  stm_version_t l;

  assert(tx->merge);
# if OPERATION_LOGGING != OPLOG_NONE
  assert(OP_VALID(tx, tx->merge->context.current));
# endif /* OPERATION_LOGGING != OPLOG_NONE */
  assert(READ_POINTER_VALID(tx, r));

#ifdef READ_SET_SOURCE
  /* Original read did not come from memory */
  if (WRITE_VALID_FAST(tx, r->source)) {
    /* Did we previously write the same address? */
    const w_entry_t *w = POINTER_FROM_WRITE(tx, r->source);
    /* It is unlikely that the write has been reverted */
    if (likely(w->mask)) {
update:
      /* Get value from write set if possible */
      /* Most recent write must not have occurred after the operation being merged */
      assert(!OP_VALID(tx, w->op) || w->op.idx <= r->op.idx);
      r->value = (r->value & ~w->mask) | (w->value & w->mask);
      r->version = w->version;
      return r->value;
    } else {
# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
      /* Write has been reverted, source of the read must change */
      const stm_read_t rt = READ_FROM_POINTER(tx, r);
      if (
#  if READ_SET == RW_ADAPTIVE
        kh_size(tx->r_set.hash)
#  else
        1
#  endif /* READ_SET == RW_ADAPTIVE */
      ) {
        khiter_t it = kh_get(r_set, tx->r_set.hash, rt);
        assert(it != kh_end(tx->r_set.hash));
        kh_del(r_set, tx->r_set.hash, it);
      }
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */

#if OPERATION_LOGGING == OPLOG_FULL
      /* Set the source to the previous write */
      if (WRITE_VALID_FAST(tx, w->addr_prev)) {
        r->source = w->addr_prev;
        w = POINTER_FROM_WRITE(tx, w->addr_prev);
        assert(w->mask);
        goto update;
      } else
#endif /* OPERATION_LOGGING == OPLOG_FULL */
        r->source = STM_INVALID_WRITE;

# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
      if (
#  if READ_SET == RW_ADAPTIVE
        kh_size(tx->r_set.hash)
#  else
        1
#  endif /* READ_SET == RW_ADAPTIVE */
      ) {
        int ret;
        assert(r != &tx->r_set.entries[READ_RESERVED_IDX]);
        kh_put(r_set, tx->r_set.hash, rt, &ret);
        assert(ret > 0);
      }
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
    }
  }
#endif /* READ_SET_SOURCE */

  /* Read lock, value, lock */
 restart:
  l = LOCK_READ_ACQ(r->lock);
 restart_no_load:
  if (LOCK_GET_OWNED(r->addr, l)) {
#if DETECTION == TIME_BASED
    w_entry_unique_t *wu = (w_entry_unique_t *)LOCK_GET_ADDR(l);
    if (WRITE_UNIQUE_POINTER_VALID(tx, wu)) {
      r->version = wu->version;
      goto read;
    }
#endif /* DETECTION == TIME_BASED */

    /* Spin while locked (should not last long) */
    goto restart;
  } else {
#if DETECTION == TIME_BASED
    /* Check timestamp */
    assert(r->version <= LOCK_GET_TIMESTAMP(l));
    if (LOCK_GET_TIMESTAMP(l) > tx->end_next)
      stm_rollback(tx, STM_ABORT_VAL_READ);
    r->version = LOCK_GET_TIMESTAMP(l);
#endif /* DETECTION == TIME_BASED */
  }
read:
  r->value = ATOMIC_LOAD_ACQ(r->addr);
#if DETECTION == TIME_BASED
  stm_version_t l2 = LOCK_READ_ACQ(r->lock);
  if (l != l2) {
    l = l2;
    goto restart_no_load;
  }
#endif /* DETECTION == TIME_BASED */

  return r->value;
}
#endif /* CM == CM_MERGE */

static INLINE stm_word_t
stm_wbctl_RaR(stm_tx_t *tx, const stm_word_t *addr)
{
  /* Possible optimization: avoid adding to read set. */
  return stm_wbctl_read(tx, addr
#ifdef READ_SET_TAGGED
    , 0
#endif /* READ_SET_TAGGED */
  );
}

static INLINE stm_word_t
stm_wbctl_RaW(stm_tx_t *tx, const stm_word_t *addr)
{
  /* Cannot be much better than regular due to mask == 0 case. */
  return stm_wbctl_read(tx, addr
#ifdef READ_SET_TAGGED
    , 0
#endif /* READ_SET_TAGGED */
  );
}

static INLINE stm_word_t
stm_wbctl_RfW(stm_tx_t *tx, const stm_word_t *addr)
{
  /* We need to return the value here, so write with mask=0 is not enough. */
  return stm_wbctl_read(tx, addr
#ifdef READ_SET_TAGGED
    , 0
#endif /* READ_SET_TAGGED */
  );
}

static INLINE void
stm_wbctl_WaR(stm_tx_t *tx, stm_word_t *addr, const stm_word_t value, const stm_word_t mask)
{
  /* Probably no optimization can be done here. */
  stm_wbctl_write(tx, addr, value, mask);
}

static INLINE void
stm_wbctl_WaW(stm_tx_t *tx, stm_word_t *addr, const stm_word_t value, const stm_word_t mask)
{
  /* Get the write set entry. */
  w_entry_unique_t *wu = int_stm_did_store_unique(tx, (stm_word_t *)addr);
  assert(wu);
  w_entry_t *w = stm_has_written_current(tx, wu
#if OPERATION_LOGGING == OPLOG_FULL
    , int_stm_get_log(tx)
#endif /* OPERATION_LOGGING == OPLOG_FULL */
  );
  assert(w);

  /* Update directly into the write set. */
  w->value = (w->value & ~mask) | (value & mask);
  w->mask |= mask;
}

static INLINE void
stm_wbctl_do_commit(stm_tx_t *tx
#if DETECTION == TIME_BASED
  , stm_version_t l
#endif /* DETECTION == TIME_BASED */
) {
  /* Install new versions, drop locks and set new timestamp */
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  for (const w_entry_unique_t *wu = tx->w_set_unique.entries + WRITE_RESERVED_IDX + 1; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#else
  for (const w_entry_unique_t *wu = tx->w_set_unique.entries; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
  {
    if (WRITE_VALID_FAST(tx, wu->latest)) {
      const w_entry_t *w = POINTER_FROM_WRITE(tx, wu->latest);
# if OPERATION_LOGGING == OPLOG_FULL
      assert(!STM_SAME_OP(w->op, STM_SPECIAL_OP));
# endif /* OPERATION_LOGGING == OPLOG_FULL */
      assert(w->mask);
      if (w->mask == ~(stm_word_t)0)
        ATOMIC_STORE(wu->addr, w->value);
      else
        ATOMIC_STORE(wu->addr, (ATOMIC_LOAD(wu->addr) & ~w->mask) | (w->value & w->mask));
    }

#if DETECTION == TIME_BASED
    /* Only drop lock for last covered address in write set (cannot be "no drop") */
    if (!wu->no_drop) {
      assert(l >= wu->version);
      assert(LOCK_GET_OWNED(wu->addr, LOCK_READ_ACQ(wu->lock)) && WRITE_UNIQUE_POINTER_VALID(tx, (w_entry_unique_t *)LOCK_GET_ADDR(LOCK_READ_ACQ(wu->lock))) && ((w_entry_unique_t *)(LOCK_GET_ADDR(LOCK_READ_ACQ(wu->lock))))->lock == wu->lock);
      LOCK_WRITE_REL(wu->lock, LOCK_SET_TIMESTAMP(wu, l, 0));
    } else {
# ifndef NDEBUG
      if (WRITE_VALID_FAST(tx, wu->latest)) {
        stm_version_t l2 = LOCK_READ(wu->lock);
        assert(LOCK_GET_WRITE(wu->addr, l2) && WRITE_UNIQUE_POINTER_VALID(tx, (w_entry_unique_t *)LOCK_GET_ADDR(l2)));
      }
# endif /* NDEBUG */
    }
#endif /* DETECTION == TIME_BASED */
  }
}

static INLINE int
stm_wbctl_commit(stm_tx_t *tx) {
#if DETECTION == TIME_BASED
  stm_version_t l;
#endif /* DETECTION == TIME_BASED */

  PRINT_DEBUG("==> stm_wbctl_commit(%p[%lu])\n", tx, (unsigned long)tx->end);

#if DETECTION == TIME_BASED
revalidate_relock:
  assert(tx->w_set_unique.nb_acquired == 0);
# if !defined(MERGE_UNLOCK) && (CM == CM_MERGE || defined(MERGE_LOCK_CONFLICT))
  tx->revalidate &= ~REVALIDATE_RELOCK;
# endif /* MERGE_UNLOCK (CM == CM_MERGE || MERGE_LOCK_CONFLICT) */

  /* Acquire locks on read set */
  if (!stm_wbctl_lock_all(tx)) {
# ifdef TM_STATISTICS
    ++tx->stat_relocks;
# endif /* TM_STATISTICS */
    goto revalidate_relock;
  }

# if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  assert(tx->w_set_unique.nb_acquired || tx->w_set_unique.nb_entries == 1);
# else
  assert(tx->w_set_unique.nb_acquired || !tx->w_set_unique.nb_entries);
# endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
#endif /* DETECTION == TIME_BASED */

#ifdef IRREVOCABLE_ENABLED
  /* Verify if there is an irrevocable transaction once all locks have been acquired */
# ifdef IRREVOCABLE_IMPROVED
  /* FIXME: it is bogus. the status should be changed to idle otherwise stm_quiesce will not progress */
  if (unlikely(!tx->irrevocable)) {
    do {
      l = ATOMIC_LOAD(&_tinystm.irrevocable);
      /* If the irrevocable transaction have encountered an acquired lock, abort */
      if (l == 2) {
        stm_rollback(tx, STM_ABORT_IRREVOCABLE);
        return 0;
      }
    } while (l);
  }
# else /* ! IRREVOCABLE_IMPROVED */
  if (!tx->irrevocable && ATOMIC_LOAD(&_tinystm.irrevocable)) {
    stm_rollback(tx, STM_ABORT_IRREVOCABLE);
    return 0;
  }
# endif /* ! IRREVOCABLE_IMPROVED */
#endif /* IRREVOCABLE_ENABLED */

revalidate_clock:
#if DETECTION == TIME_BASED
# if !defined(MERGE_UNLOCK) && CM == CM_MERGE
  tx->revalidate &= ~REVALIDATE_CLOCK;
# endif /* !MERGE_UNLOCK && CM == CM_MERGE */
  /* Get commit timestamp (may exceed VERSION_MAX by up to MAX_THREADS) */
  l = FETCH_INC_CLOCK + 1;
#endif /* DETECTION == TIME_BASED */

#ifdef IRREVOCABLE_ENABLED
  if (unlikely(tx->irrevocable))
    goto release_locks;
#endif /* IRREVOCABLE_ENABLED */

  /* Try to validate (only if a concurrent transaction has committed since tx->end) */
  if (
#if DETECTION == TIME_BASED
    tx->end != l - 1
#endif /* DETECTION */
  ) {
    int ret = stm_wbctl_extend(tx
#if DETECTION == TIME_BASED
      , l
#endif /* DETECTION == TIME_BASED */
    );
    if (!ret) {
      /* Cannot commit */
      stm_rollback(tx, STM_ABORT_VAL_COMMIT);
      return 0;
#if !defined(MERGE_UNLOCK) && (DETECTION == TIME_BASED) && (CM == CM_MERGE || defined(MERGE_LOCK_CONFLICT))
    } else if (ret == -1) {
      if (tx->revalidate & REVALIDATE_RELOCK) {
# ifdef TM_STATISTICS
        ++tx->stat_relocks;
# endif /* TM_STATISTICS */
        goto revalidate_relock;
      }
      assert(tx->revalidate & REVALIDATE_CLOCK);
      goto revalidate_clock;
#endif /* !MERGE_UNLOCK && (DETECTION == TIME_BASED) && (CM == CM_MERGE || MERGE_LOCK_CONFLICT) */
    }
#if DETECTION == TIME_BASED
# ifdef MERGE_UNLOCK
    if (!tx->w_set_unique.nb_acquired) {
#  ifdef TM_STATISTICS
      ++tx->stat_relocks;
#  endif /* TM_STATISTICS */
      goto revalidate_relock;
    }
# endif /* MERGE_UNLOCK */
#endif /* DETECTION */
  }

#if !defined(MERGE_UNLOCK) && (CM == CM_MERGE || defined(MERGE_LOCK_CONFLICT)) && (DETECTION == TIME_BASED)
  assert(!tx->revalidate);
#endif /* !MERGE_UNLOCK && (CM == CM_MERGE || MERGE_LOCK_CONFLICT) && (DETECTION == TIME_BASED) */

#ifdef IRREVOCABLE_ENABLED
release_locks:
#endif /* IRREVOCABLE_ENABLED */

  /* Install new versions, drop locks and set new timestamp */
    stm_wbctl_do_commit(tx
#if DETECTION == TIME_BASED
      , l
#endif /* DETECTION == TIME_BASED */
    );

  return 1;
}

#endif /* _STM_WBCTL_H_ */
