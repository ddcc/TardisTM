/*
 * File:
 *   stm_wt.h
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

#ifndef _STM_WT_H_
#define _STM_WT_H_

#include "stm_internal.h"
#include "atomic.h"

static INLINE int
stm_wt_validate(stm_tx_t *tx)
{
  r_entry_t *r;
  stm_version_t l;
  stm_word_t contents;
  tx_conflict_t conflict;
  stm_tx_policy_t decision;

  PRINT_DEBUG("==> stm_wt_validate(%p[%lu])\n", tx, (unsigned long)tx->end);

  /* Validate reads */
# if READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE
  for (stm_read_t rt = { .idx = READ_RESERVED_IDX + 1 }; READ_VALID(tx, rt); ++rt.idx)
# else
  for (stm_read_t rt = { .idx = 0 }; READ_VALID(tx, rt); ++rt.idx)
# endif /* READ_SET == RW_HASH_TABLE || READ_SET == RW_ADAPTIVE */
  {
restart:
    r = POINTER_FROM_READ(tx, rt);
    assert(READ_POINTER_VALID(tx, r));
    if (!r->lock)
      continue;
    /* Read lock */
    l = LOCK_READ(r->lock);
    /* Unlocked and still the same version? */
    if (LOCK_GET_OWNED(r->addr, l)) {
      /* Do we own the lock? */
      w_entry_unique_t *wu = (w_entry_unique_t *)LOCK_GET_ADDR(l);
      /* Simply check if address falls inside our write set (avoids non-faulting load) */
      if (WRITE_UNIQUE_POINTER_VALID(tx, wu))
        continue;

      /* Locked by another transaction: cannot validate */
      conflict.entries.type = STM_RW_CONFLICT;
      conflict.entries.e1 = ENTRY_FROM_READ_POINTER(tx, r);
      conflict.entries.e2 = ENTRY_FROM_WRITE(tx, wu->latest);
#ifdef CONFLICT_TRACKING
      conflict.other = w->tx;
      conflict.status = w->tx->status;
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
      conflict.lock = w->lock;
#endif /* CONTENDED_LOCK_TRACKING */
      decision = stm_conflict_handle(tx, &conflict);
    } else {
#if DETECTION == TIME_BASED
      /* Same version: OK */
      contents = LOCK_GET_TIMESTAMP(l);
      if (contents == r->version)
        continue;
#endif /* DETECTION */

      /* Other version: cannot validate */
      conflict.entries.type = STM_RD_VALIDATE;
      conflict.entries.e1 = ENTRY_FROM_READ_POINTER(tx, r);
      conflict.entries.e2 = ENTRY_INVALID;
#ifdef CONFLICT_TRACKING
      conflict.other = NULL;
      conflict.status = 0;
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
      conflict.lock = NULL;
#endif /* CONTENDED_LOCK_TRACKING */
      decision = stm_conflict_handle(tx, &conflict);
    }

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

  return 1;
}

#if DETECTION == TIME_BASED
/*
 * Extend snapshot range.
 */
static INLINE int
stm_wt_extend(stm_tx_t *tx
#if DETECTION == TIME_BASED
  , stm_version_t now
#endif /* DETECTION == TIME_BASED */
) {
  PRINT_DEBUG("==> stm_wt_extend(%p[%lu])\n", tx, (unsigned long)tx->end);

#ifdef UNIT_TX
  /* Extension is disabled */
  if (tx->attr.no_extend)
    return 0;
#endif /* UNIT_TX */

#  ifdef TM_STATISTICS
  ++tx->stat_extensions;
#  endif /* TM_STATISTICS */

  /* No need to check clock overflow here. The clock can exceed up to MAX_THREADS and it will be reset when the quiescence is reached. */

  /* Try to validate read set */
  if (stm_wt_validate(tx)) {
    /* It works: we can extend until now */
    tx->end = now;
    return 1;
  }
  return 0;
}
#endif /* DETECTION == TIME_BASED */

static INLINE void
stm_wt_rollback(stm_tx_t *tx)
{
  stm_version_t t;

  PRINT_DEBUG("==> stm_wt_rollback(%p[%lu])\n", tx, (unsigned long)tx->end);

  assert(IS_ACTIVE(tx->status));

  t = 0;
  /* Undo writes and drop locks */
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  for (const w_entry_unique_t *wu = tx->w_set_unique.entries + WRITE_RESERVED_IDX + 1; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#else
  for (const w_entry_unique_t *wu = tx->w_set_unique.entries; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
  {
    stm_word_t j;
    if (!wu->lock || !WRITE_VALID(tx, wu->latest))
      continue;
    const w_entry_t *w = POINTER_FROM_WRITE(tx, wu->latest);
    /* Restore previous value */
    if (w->mask != 0)
      ATOMIC_STORE(wu->addr, w->value);
    if (WRITE_UNIQUE_VALID(tx, wu->next))
      continue;
    /* Incarnation numbers allow readers to detect dirty reads */
    j = LOCK_GET_INCARNATION(wu->version) + 1;
    if (j > INCARNATION_MAX) {
      /* Simple approach: write new version (might trigger unnecessary aborts) */
      if (t == 0) {
        /* Get new version (may exceed VERSION_MAX by up to MAX_THREADS) */
        t = FETCH_INC_CLOCK + 1;
      }
#if DETECTION == TIME_BASED
      LOCK_WRITE_REL(wu->lock, LOCK_SET_TIMESTAMP(wu, t, LOCK_READ_ACQ(wu->lock)));
#endif /* DETECTION */
    } else {
      /* Use new incarnation number */
      LOCK_WRITE_REL(wu->lock, LOCK_UPD_INCARNATION(wu->version, j));
    }
  }
  /* Make sure that all lock releases become visible */
  ATOMIC_MB_WRITE;
}

static INLINE stm_word_t
stm_wt_read(stm_tx_t *tx, const stm_word_t *addr
#ifdef READ_SET_TAGGED
  , uintptr_t tag
#endif /* READ_SET_TAGGED */
) {
  const stm_lock_t *lock;
  stm_version_t l, l2;
  stm_word_t value;
#if DETECTION == TIME_BASED
  stm_version_t version;
#endif /* DETECTION == TIME_BASED */

  PRINT_DEBUG2("==> stm_wt_read(t=%p[%lu],a=%p)\n", tx, (unsigned long)tx->end, addr);

  assert(IS_ACTIVE(tx->status));

  /* Get reference to lock */
  lock = GET_LOCK(addr);

  /* Note: we could check for duplicate reads and get value from read set */

  /* Read lock, value, lock */
restart:
  l = LOCK_READ_ACQ(lock);
restart_no_load:
  if (likely(!LOCK_GET_WRITE(addr, l))) {
    /* Not locked */
    value = ATOMIC_LOAD_ACQ(addr);
    l2 = LOCK_READ_ACQ(lock);
    if (l != l2) {
      l = l2;
      goto restart_no_load;
    }

#ifdef IRREVOCABLE_ENABLED
    /* In irrevocable mode, no need check timestamp nor add entry to read set */
    if (unlikely(tx->irrevocable))
      goto no_check;
#endif /* IRREVOCABLE_ENABLED */

#if DETECTION == TIME_BASED
  /* Check timestamp */
    version = LOCK_GET_TIMESTAMP(l);
#endif /* DETECTION == TIME_BASED */

#ifdef NO_DUPLICATES_IN_RW_SETS
    if (stm_has_read(tx, addr) != NULL) {
      return value;
#endif /* NO_DUPLICATES_IN_RW_SETS */

    /* Add to read set (update transactions only) */
    stm_add_to_rs(tx, addr
#if DETECTION == TIME_BASED
      , lock, version
#endif /* DETECTION */
#ifdef READ_SET_TAGGED
      , tag
#endif /* READ_SET_TAGGED */
#if READ_SET_SOURCE
      , STM_INVALID_WRITE
#endif /* READ_SET_SOURCE */
    );

#if DETECTION == TIME_BASED
    /* Valid version? */
    if (unlikely(version > tx->end)) {
      /* No: try to extend first (except for read-only transactions: no read set) */
      if (tx->attr.read_only || !stm_wt_extend(tx
#if DETECTION == TIME_BASED
          , GET_CLOCK
#endif /* DETECTION == TIME_BASED */
        )) {
        /* Not much we can do: abort */
        stm_rollback(tx, STM_ABORT_VAL_READ);
        return 0;
      }
      /* Worked: we now have a good version (version <= tx->end) */
    }
#endif /* DETECTION == TIME_BASED */

#ifdef IRREVOCABLE_ENABLED
no_check:
#endif /* IRREVOCABLE_ENABLED */
    /* We have a good version: return value */
    return value;
  } else {
    /* Locked */
    /* Do we own the lock? */
    w_entry_unique_t *wu = (w_entry_unique_t *)LOCK_GET_ADDR(l);

    /* Simply check if address falls inside our write set (avoids non-faulting load) */
    if (likely(WRITE_UNIQUE_POINTER_VALID(tx, wu))) {
      /* Yes: we have a version locked by us that was valid at write time */
      value = ATOMIC_LOAD(addr);
      /* No need to add to read set (will remain valid) */
      return value;
    }

#ifdef UNIT_TX
    if (l == LOCK_UNIT) {
      /* Data modified by a unit store: should not last long => retry */
      goto restart;
    }
#endif /* UNIT_TX */

    /* Conflict: CM kicks in (we could also check for duplicate reads and get value from read set) */
#if defined(IRREVOCABLE_ENABLED) && defined(IRREVOCABLE_IMPROVED)
    if (tx->irrevocable && ATOMIC_LOAD(&_tinystm.irrevocable) == 1)
      ATOMIC_STORE(&_tinystm.irrevocable, 2);
#endif /* defined(IRREVOCABLE_ENABLED) && defined(IRREVOCABLE_IMPROVED) */
#if defined(IRREVOCABLE_ENABLED)
    if (tx->irrevocable) {
      /* Spin while locked */
      goto restart;
    }
#endif /* defined(IRREVOCABLE_ENABLED) */

    tx_conflict_t conflict = {
      .entries.type = STM_RW_CONFLICT,
      .entries.e1 = ENTRY_FROM_WRITE(tx, wu->latest),
      .entries.e2 = ENTRY_INVALID,
#ifdef CONFLICT_TRACKING
      .other = w->tx,
      .status = w->tx->status,
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
      .lock = lock,
#endif /* CONTENDED_LOCK_TRACKING */
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
}

static INLINE w_entry_t *
stm_wt_write(stm_tx_t *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
  const stm_lock_t *lock;
  stm_version_t l;
#if DETECTION == TIME_BASED
  stm_version_t version;
  r_entry_t *r;
#endif /* DETECTION == TIME_BASED */
  w_entry_unique_t *wu = NULL, *prev = NULL;
  w_entry_t *w;

  PRINT_DEBUG2("==> stm_wt_write(t=%p[%lu],a=%p,d=%p-%lu,m=0x%lx)\n",
               tx, (unsigned long)tx->end, addr, (void *)value, (unsigned long)value, (unsigned long)mask);

  /* Get reference to lock */
  lock = GET_LOCK(addr);

  /* Try to acquire lock */
restart:
  l = LOCK_READ_ACQ(lock);
restart_no_load:
  if (LOCK_GET_OWNED(addr, l)) {
    /* Locked */

#ifdef UNIT_TX
    if (l == LOCK_UNIT) {
      /* Data modified by a unit store: should not last long => retry */
      goto restart;
    }
#endif /* UNIT_TX */

    /* Do we own the lock? */
    wu = (w_entry_unique_t *)LOCK_GET_ADDR(l);
    /* Simply check if address falls inside our write set (avoids non-faulting load) */
    if (likely(WRITE_UNIQUE_POINTER_VALID(tx, wu))) {
      w = WRITE_VALID(tx, wu->latest) ? POINTER_FROM_WRITE(tx, wu->latest) : NULL;
      if (mask == 0) {
        /* No need to insert new entry or modify existing one */
        return w;
      }
      prev = wu;
      /* Did we previously write the same address? */
      while (1) {
        if (addr == prev->addr) {
          if (w->mask == 0) {
            /* Remember old value */
            w->value = ATOMIC_LOAD(addr);
            w->mask = mask;
          }
          /* Yes: only write to memory */
          if (mask != ~(stm_word_t)0)
            value = (ATOMIC_LOAD(addr) & ~mask) | (value & mask);
          ATOMIC_STORE(addr, value);
          return w;
        }
        if (!WRITE_UNIQUE_VALID(tx, prev->next)) {
          /* Remember last entry in linked list (for adding new entry) */
          break;
        }
        prev = POINTER_FROM_WRITE_UNIQUE(tx, prev->next);
      }
      /* Must add to write set */
      wu = stm_add_to_ws_unique(tx, addr);
      if (tx->w_set.nb_entries == tx->w_set.size)
        stm_rollback(tx, STM_ABORT_EXTEND_WS);
      w = &tx->w_set.entries[tx->w_set.nb_entries];
#if DETECTION == TIME_BASED
      /* Get version from previous write set entry (all entries in linked list have same version) */
      wu->version = prev->version;
#endif /* DETECTION == TIME_BASED */
      goto do_write;
    }
    /* Conflict: CM kicks in */
#if defined(IRREVOCABLE_ENABLED) && defined(IRREVOCABLE_IMPROVED)
    if (tx->irrevocable && ATOMIC_LOAD(&_tinystm.irrevocable) == 1)
      ATOMIC_STORE(&_tinystm.irrevocable, 2);
#endif /* defined(IRREVOCABLE_ENABLED) && defined(IRREVOCABLE_IMPROVED) */
#if defined(IRREVOCABLE_ENABLED)
    if (tx->irrevocable) {
      /* Spin while locked */
      goto restart;
    }
#endif /* defined(IRREVOCABLE_ENABLED) */
    tx_conflict_t conflict = {
      .entries.type = STM_WW_CONFLICT,
      .entries.e1 = ENTRY_FROM_WRITE(tx, wu->latest),
      .entries.e2 = ENTRY_INVALID,
#ifdef CONFLICT_TRACKING
      .other = w->tx,
      .status = w->tx->status,
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
      .lock = lock,
#endif /* CONTENDED_LOCK_TRACKING */
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
  /* Not locked */
#if DETECTION == TIME_BASED
  /* Handle write after reads (before CAS) */
  version = LOCK_GET_TIMESTAMP(l);
#endif /* DETECTION == TIME_BASED */
#ifdef IRREVOCABLE_ENABLED
  /* In irrevocable mode, no need to revalidate */
  if (tx->irrevocable)
    goto acquire_no_check;
#endif /* IRREVOCABLE_ENABLED */
acquire:
#if DETECTION == TIME_BASED
  if (unlikely(version > tx->end)) {
    /* We might have read an older version previously */
#ifdef UNIT_TX
    if (tx->attr.no_extend) {
      stm_rollback(tx, STM_ABORT_VAL_WRITE);
      return NULL;
    }
#endif /* UNIT_TX */
    if ((r = stm_has_read(tx, addr)) != NULL) {
      /* Read version must be older (otherwise, tx->end >= version) */
      /* Not much we can do: abort */
      tx_conflict_t conflict = {
        .entries.type = STM_WR_VALIDATE,
        .entries.e1 = ENTRY_FROM_READ_POINTER(tx, r),
        .entries.e2 = wu ? ENTRY_FROM_WRITE(tx, wu->latest) : ENTRY_INVALID,
#ifdef CONFLICT_TRACKING
        .other = NULL,
        .status = 0,
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
        .lock = lock,
#endif /* CONTENDED_LOCK_TRACKING */
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
  }
#endif /* DETECTION */
  /* Acquire lock (ETL) */
acquire_no_check:
  /* Add address to unique write set */
  assert(!wu || !WRITE_UNIQUE_POINTER_VALID(tx, wu));
  wu = stm_add_to_ws_unique(tx, addr);

  if (tx->w_set.nb_entries == tx->w_set.size)
    stm_allocate_ws_entries(tx, 1);
  w = &tx->w_set.entries[tx->w_set.nb_entries];
  if (LOCK_WRITE_CAS(lock, l, LOCK_SET_ADDR_WRITE(wu, l)) == 0) {
    --tx->w_set_unique.nb_entries;
    goto restart;
  }
#if DETECTION == TIME_BASED
  /* We store the old value of the lock (timestamp and incarnation) */
  wu->version = l;
#endif /* DETECTION == TIME_BASED */
  /* We own the lock here (ETLf) */
do_write:
  /* Add address to write set */
  wu->addr = addr;
  wu->lock = lock;
  w->mask = mask;
  if (mask == 0) {
    /* Do not write anything */
#ifndef NDEBUG
    w->value = 0;
#endif /* ! NDEBUG */
  } else {
    /* Remember old value */
    w->value = ATOMIC_LOAD(addr);
  }
  if (mask != 0) {
    if (mask != ~(stm_word_t)0)
      value = (w->value & ~mask) | (value & mask);
    ATOMIC_STORE(addr, value);
  }
  wu->next = STM_INVALID_WRITE_UNIQUE;
  if (prev != NULL) {
    /* Link new entry in list */
    prev->next = WRITE_UNIQUE_FROM_POINTER(tx, wu);
  }
  tx->w_set.nb_entries++;

  wu->latest = WRITE_FROM_POINTER(tx, w);
  return w;
}

static INLINE stm_word_t
stm_wt_RaR(stm_tx_t *tx, stm_word_t *addr)
{
  /* TODO same as fast read but no need to add into the RS */
  return stm_wt_read(tx, addr);
}

static INLINE stm_word_t
stm_wt_RaW(stm_tx_t *tx, stm_word_t *addr)
{
#ifndef NDEBUG
  const stm_lock_t *lock;
  stm_version_t l;
  w_entry_unique_t *wu;

  /* Get reference to lock */
  lock = GET_LOCK(addr);
  l = LOCK_READ_ACQ(lock);
  /* Does the lock owned? */
  assert(LOCK_GET_WRITE(addr, l));
  /* Do we own the lock? */
  wu = (w_entry_unique_t *)LOCK_GET_ADDR(l);
  assert(WRITE_UNIQUE_POINTER_VALID(tx, wu));
#endif /* ! NDEBUG */

  /* Read directly from memory. */
  return *addr;
}

static INLINE stm_word_t
stm_wt_RfW(stm_tx_t *tx, stm_word_t *addr)
{
  /* Acquire lock as write. */
  stm_wt_write(tx, addr, 0, 0);
  /* Now the lock is owned, read directly from memory is safe. */
  return *addr;
}

static INLINE void
stm_wt_WaR(stm_tx_t *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
  /* Probably no optimization can be done here. */
  stm_wt_write(tx, addr, value, mask);
}

static INLINE void
stm_wt_WaW(stm_tx_t *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
#ifndef NDEBUG
  const stm_lock_t *lock;
  stm_version_t l;
  w_entry_unique_t *wu;

  /* Get reference to lock */
  lock = GET_LOCK(addr);
  l = LOCK_READ_ACQ(lock);
  /* Does the lock owned? */
  assert(LOCK_GET_WRITE(addr, l));
  /* Do we own the lock? */
  wu = (w_entry_unique_t *)LOCK_GET_ADDR(l);
  assert(WRITE_UNIQUE_POINTER_VALID(tx, wu));
  /* in WaW, mask can never be 0 */
  assert(mask != 0);
#endif /* ! NDEBUG */
  if (mask != ~(stm_word_t)0) {
    value = (ATOMIC_LOAD(addr) & ~mask) | (value & mask);
  }
  ATOMIC_STORE(addr, value);
}

static INLINE int
stm_wt_commit(stm_tx_t *tx)
{
  stm_version_t t;

  PRINT_DEBUG("==> stm_wt_commit(%p[%lu])\n", tx, (unsigned long)tx->end);

  /* Update transaction */
#ifdef IRREVOCABLE_ENABLED
  /* Verify if there is an irrevocable transaction once all locks have been acquired */
# ifdef IRREVOCABLE_IMPROVED
  /* FIXME: it is bogus. the status should be changed to idle otherwise stm_quiesce will not progress */
  if (unlikely(!tx->irrevocable)) {
    do {
      t = ATOMIC_LOAD(&_tinystm.irrevocable);
      /* If the irrevocable transaction have encountered an acquired lock, abort */
      if (t == 2) {
        stm_rollback(tx, STM_ABORT_IRREVOCABLE);
        return 0;
      }
    } while (t);
  }
# else /* ! IRREVOCABLE_IMPROVED */
  if (!tx->irrevocable && ATOMIC_LOAD(&_tinystm.irrevocable)) {
    stm_rollback(tx, STM_ABORT_IRREVOCABLE);
    return 0;
  }
# endif /* ! IRREVOCABLE_IMPROVED */
#endif /* IRREVOCABLE_ENABLED */

#if DETECTION == TIME_BASED
  /* Get commit timestamp (may exceed VERSION_MAX by up to MAX_THREADS) */
  t = FETCH_INC_CLOCK + 1;
#endif /* DETECTION == TIME_BASED */

#ifdef IRREVOCABLE_ENABLED
  if (unlikely(tx->irrevocable))
    goto release_locks;
#endif /* IRREVOCABLE_ENABLED */

  /* Try to validate (only if a concurrent transaction has committed since tx->end) */
  if (
#if DETECTION == TIME_BASED
      unlikely(tx->end != t - 1 && !stm_wt_validate(tx))
#endif /* DETECTION */
  ) {
    /* Cannot commit */
    stm_rollback(tx, STM_ABORT_VAL_COMMIT);
    return 0;
  }

#ifdef IRREVOCABLE_ENABLED
release_locks:
#endif /* IRREVOCABLE_ENABLED */

  /* Make sure that the updates become visible before releasing locks */
  ATOMIC_MB_WRITE;
  /* Drop locks and set new timestamp */
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  for (const w_entry_unique_t *wu = tx->w_set_unique.entries + WRITE_RESERVED_IDX + 1; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#else
  for (const w_entry_unique_t *wu = tx->w_set_unique.entries; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
  {
    if (!wu->lock)
      continue;
    if (!WRITE_UNIQUE_VALID(tx, wu->next)) {
      /* No need for CAS (can only be modified by owner transaction) */
#if DETECTION == TIME_BASED
      LOCK_WRITE(wu->lock, LOCK_SET_TIMESTAMP(wu, t, LOCK_READ_ACQ(wu->lock)));
#endif /* DETECTION */

    }
  }
  /* Make sure that all lock releases become visible */
  /* TODO: is ATOMIC_MB_WRITE required? */
  ATOMIC_MB_WRITE;
end:
  return 1;
}

#endif /* _STM_WT_H_ */

