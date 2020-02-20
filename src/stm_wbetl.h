/*
 * File:
 *   stm_wbetl.h
 * Author(s):
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * Description:
 *   STM internal functions for Write-back ETL.
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

#ifndef _STM_WBETL_H_
#define _STM_WBETL_H_

#include "stm_internal.h"
#include "atomic.h"

#if DESIGN == WRITE_BACK_ETL_VR && ! defined(TRANSACTION_OPERATIONS)
# error "WRITE_BACK_ETL_VR requires TRANSACTION_OPERATIONS"
#endif /* DESIGN == WRITE_BACK_ETL_VR && ! defined(TRANSACTION_OPERATIONS) */

static INLINE int
stm_wbetl_validate(stm_tx_t *tx)
{
  r_entry_t *r;
  stm_version_t l;
  stm_word_t contents;
  stm_tx_policy_t decision;
  tx_conflict_t conflict;

  PRINT_DEBUG("==> stm_wbetl_validate(%p[%lu])\n", tx, (unsigned long)tx->end);

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
    l = LOCK_READ_ACQ(r->lock);
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
      conflict.other = wu->tx;
      conflict.status = wu->tx->status;
#endif /* CONFLICT_TRACKING */
#ifdef CONTENDED_LOCK_TRACKING
      conflict.lock = wu->lock;
#endif /* CONTENDED_LOCK_TRACKING */
      decision = stm_conflict_handle(tx, &conflict);
    } else {
#if DETECTION == TIME_BASED
      /* Same version: OK */
      contents = LOCK_GET_TIMESTAMP(l);
      if (contents == r->version)
        continue;
#endif /* DETECTION == TIME_BASED */

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

/*
 * Extend snapshot range.
 */
static INLINE int
stm_wbetl_extend(stm_tx_t *tx
#if DETECTION == TIME_BASED
  , stm_version_t now
#endif /* DETECTION == TIME_BASED */
) {
  PRINT_DEBUG("==> stm_wbetl_extend(%p[%lu])\n", tx, (unsigned long)tx->end);

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
  if (stm_wbetl_validate(tx)) {
    /* It works: we can extend until now */
    tx->end = now;
    return 1;
  }
  return 0;
}

static INLINE void
stm_wbetl_rollback(stm_tx_t *tx)
{
#ifdef TRANSACTION_OPERATIONS
  stm_word_t t;
#endif /* TRANSACTION_OPERATIONS */
  PRINT_DEBUG("==> stm_wbetl_rollback(%p[%lu])\n", tx, (unsigned long)tx->end);

  assert(IS_ACTIVE(tx->status));
#ifdef TRANSACTION_OPERATIONS
  /* Set status to ABORTING */
  t = tx->status;
  if (GET_STATUS(t) == TX_KILLING || (GET_STATUS(t) == TX_ACTIVE_BIT && UPDATE_STATUS(tx->status, t, t + TX_ABORTED) == 0)) {
    /* We have been killed */
    assert(GET_STATUS(tx->status) == TX_KILLING);
    /* Release locks */
    stm_drop(tx);
    return;
  }
#endif /* TRANSACTION_OPERATIONS */

  /* Drop locks */
  if (tx->w_set_unique.has_writes > 0) {
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
    for (const w_entry_unique_t *wu = tx->w_set_unique.entries + WRITE_RESERVED_IDX + 1; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#else
    for (const w_entry_unique_t *wu = tx->w_set_unique.entries; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
    {
      if (!WRITE_UNIQUE_VALID(tx, wu->next)) {
        /* Only drop lock for last covered address in write set */
        assert(LOCK_GET_OWNED(wu->addr, LOCK_READ_ACQ(wu->lock)) && WRITE_UNIQUE_POINTER_VALID(tx, (w_entry_unique_t *)LOCK_GET_ADDR(LOCK_READ_ACQ(wu->lock))) && ((w_entry_unique_t *)(LOCK_GET_ADDR(LOCK_READ_ACQ(wu->lock))))->lock == wu->lock);
#if DETECTION == TIME_BASED
        LOCK_WRITE(wu->lock, LOCK_SET_TIMESTAMP(wu, wu->version, LOCK_READ_ACQ(wu->lock)));
#endif /* DETECTION */
      }
    }
    /* Make sure that all lock releases become visible */
    ATOMIC_MB_WRITE;
  }
}

/*
 * Load a word-sized value (invisible read).
 */
static INLINE stm_word_t
stm_wbetl_read_invisible(stm_tx_t *tx, const stm_word_t *addr
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
  w_entry_unique_t *wu;
  w_entry_t *w;
#if defined(TRANSACTION_OPERATIONS) || defined (CONFLICT_TRACKING)
  stm_word_t t;
#endif /* TRANSACTION_OPERATIONS || CONFLICT_TRACKING */
  tx_conflict_t conflict;
  stm_tx_policy_t decision;

  PRINT_DEBUG2("==> stm_wbetl_read_invisible(t=%p[%lu],a=%p)\n", tx, (unsigned long)tx->end, addr);

#ifdef TRANSACTION_OPERATIONS
  assert(IS_ACTIVE(tx->status));
#endif /* TRANSACTION_OPERATIONS */

  /* Get reference to lock */
  lock = GET_LOCK(addr);

  /* Note: we could check for duplicate reads and get value from read set */

  /* Read lock, value, lock */
restart:
  l = LOCK_READ_ACQ(lock);
restart_no_load:
  if (unlikely(LOCK_GET_WRITE(addr, l))) {
    /* Locked */
    /* Do we own the lock? */
    wu = (w_entry_unique_t *)LOCK_GET_ADDR(l);
    /* Simply check if address falls inside our write set (avoids non-faulting load) */
    if (likely(WRITE_UNIQUE_POINTER_VALID(tx, wu))) {
      /* Yes: did we previously write the same address? */
      while (1) {
        if (addr == wu->addr) {
          w = POINTER_FROM_WRITE(tx, wu->latest);
          /* Yes: get value from write set (or from memory if mask was empty) */
          value = (w->mask == 0 ? ATOMIC_LOAD(addr) : w->value);
          break;
        }
        if (!WRITE_UNIQUE_VALID(tx, wu->next)) {
          /* No: get value from memory */
          value = ATOMIC_LOAD(addr);
#ifdef TRANSACTION_OPERATIONS
          if (GET_STATUS(tx->status) == TX_KILLING) {
            stm_rollback(tx, STM_ABORT_KILLED);
            return 0;
          }
#endif /* TRANSACTION_OPERATIONS */
          break;
        }
        wu = POINTER_FROM_WRITE_UNIQUE(tx, wu->next);
      }
#if READ_SET_SOURCE
      /* Check if need to record a read of the write set */
      r_entry_t *r = int_stm_did_load(tx, addr);
      if (!r || r->source == STM_INVALID_WRITE) {
        goto add_to_read_set;
      }
#endif /* READ_SET_SOURCE */
      /* No need to add to read set (will remain valid) */
      goto return_value;
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
#ifdef IRREVOCABLE_ENABLED
    if (unlikely(tx->irrevocable)) {
      /* Spin while locked */
      goto restart;
    }
#endif /* IRREVOCABLE_ENABLED */
#ifdef TRANSACTION_OPERATIONS
    t = wu->tx->status;
    l2 = LOCK_READ_ACQ(lock);
    if (l != l2) {
      l = l2;
      goto restart_no_load;
    }
    if (t != wu->tx->status) {
      /* Transaction status has changed: restart the whole procedure */
      goto restart;
    }
# ifdef READ_LOCKED_DATA
#  ifdef IRREVOCABLE_ENABLED
    if (IS_ACTIVE(t) && !tx->irrevocable)
#  else /* ! IRREVOCABLE_ENABLED */
    if (GET_STATUS(t) == TX_ACTIVE_BIT)
#  endif /* ! IRREVOCABLE_ENABLED */
    {
      /* Read old version */
      version = ATOMIC_LOAD(&wu->version);
      /* Read data */
      value = ATOMIC_LOAD(addr);
      /* Check that data has not been written */
      if (t != wu->tx->status) {
        /* Data concurrently modified: a new version might be available => retry */
        goto restart;
      }
      if (version <= tx->end || (!tx->attr.read_only && stm_wbetl_extend(tx
#if DETECTION == TIME_BASED
        , GET_CLOCK
#endif /* DETECTION == TIME_BASED */
        ))) {
      /* Success */
#  ifdef TM_STATISTICS2
        tx->stat_locked_reads_ok++;
#  endif /* TM_STATISTICS2 */
        goto add_to_read_set;
      }
      /* Invalid version: not much we can do => fail */
#  ifdef TM_STATISTICS2
      tx->stat_locked_reads_failed++;
#  endif /* TM_STATISTICS2 */
    }
# endif /* READ_LOCKED_DATA */

    if (GET_STATUS(t) == TX_KILLING) {
      /* We can safely steal lock */
      decision = STM_KILL_OTHER;
    } else {
      conflict.entries.type = STM_RW_CONFLICT;
      conflict.entries.e1 = ENTRY_FROM_WRITE(tx, wu->latest);
      conflict.entries.e2 = ENTRY_INVALID;
# ifdef CONFLICT_TRACKING
      conflict.other = wu->tx;
      conflict.status = t;
# endif /* CONFLICT_TRACKING */
# ifdef CONTENDED_LOCK_TRACKING
      conflict.lock = lock;
# endif /* CONTENDED_LOCK_TRACKING */
      decision =
# ifdef IRREVOCABLE_ENABLED
        GET_STATUS(tx->status) == TX_IRREVOCABLE ? STM_KILL_OTHER :
# endif /* IRREVOCABLE_ENABLED */
        stm_conflict_get_decision(tx, &conflict);
      /* Handle STM_KILL_OTHER immediately */
      decision = stm_decision_kill_other(tx, &conflict, decision);
    }

    if (decision == STM_KILL_OTHER) {
      /* Steal lock */
      l2 = LOCK_SET_TIMESTAMP(wu, wu->version, l);
      if (LOCK_WRITE_CAS(lock, l, l2) == 0)
        goto restart;
      l = l2;
      goto restart_no_load;
    }
#else /* TRANSACTION_OPERATIONS */
    conflict.entries.type = STM_RW_CONFLICT;
    conflict.entries.e1 = ENTRY_FROM_WRITE(tx, wu->latest);
    conflict.entries.e2 = ENTRY_INVALID;
# ifdef CONFLICT_TRACKING
    conflict.other = wu->tx;
    conflict.status = t;
# endif /* CONFLICT_TRACKING */
# ifdef CONTENDED_LOCK_TRACKING
    conflict.lock = lock;
# endif /* CONTENDED_LOCK_TRACKING */
    decision = stm_conflict_get_decision(tx, &conflict);
#endif /* TRANSACTION_OPERATIONS */
    decision = stm_decision_implement(tx, &conflict, decision);

    switch (decision) {
      case STM_RETRY:
        goto restart;
      break;
      default:
        assert(decision == STM_KILL_SELF);
        stm_rollback(tx, conflict.entries.type);
        return 0;
      break;
    }
  } else {
    /* Not locked */
    value = ATOMIC_LOAD_ACQ(addr);
    l2 = LOCK_READ_ACQ(lock);
    if (unlikely(l != l2)) {
      l = l2;
      goto restart_no_load;
    }
#ifdef IRREVOCABLE_ENABLED
    /* In irrevocable mode, no need check timestamp nor add entry to read set */
    if (unlikely(tx->irrevocable))
      goto return_value;
#endif /* IRREVOCABLE_ENABLED */
#if DETECTION == TIME_BASED
    /* Check timestamp */
# ifdef TRANSACTION_OPERATIONS
    if (LOCK_GET_READ(l))
      version = ((w_entry_unique_t *)LOCK_GET_ADDR(l))->version;
    else
      version = LOCK_GET_TIMESTAMP(l);
# else /* TRANSACTION_OPERATIONS */
    version = LOCK_GET_TIMESTAMP(l);
# endif /* TRANSACTION_OPERATIONS */
    /* Valid version? */
    if (unlikely(version > tx->end)) {
      /* No: try to extend first (except for read-only transactions: no read set) */
      if (tx->attr.read_only || !stm_wbetl_extend(tx
#if DETECTION == TIME_BASED
        , GET_CLOCK
#endif /* DETECTION == TIME_BASED */
        )) {
        /* Not much we can do: abort */
# if DESIGN == WRITE_BACK_ETL_VR
        /* Abort caused by invisible reads */
        tx->visible_reads++;
# endif /* DESIGN == WRITE_BACK_ETL_VR */
        stm_rollback(tx, STM_ABORT_VAL_READ);
        return 0;
      }
      /* Verify that version has not been overwritten (read value has not
       * yet been added to read set and may have not been checked during
       * extend) */
      l2 = LOCK_READ_ACQ(lock);
      if (l != l2) {
        l = l2;
        goto restart_no_load;
      }
      /* Worked: we now have a good version (version <= tx->end) */
    }
#endif /* DETECTION == TIME_BASED */
#ifdef TRANSACTION_OPERATIONS
    /* Check if killed (necessary to avoid possible race on read-after-write) */
    if (GET_STATUS(tx->status) == TX_KILLING) {
      stm_rollback(tx, STM_ABORT_KILLED);
      return 0;
    }
#endif /* TRANSACTION_OPERATIONS */
  }
  /* We have a good version: add to read set (update transactions) and return value */

add_to_read_set:
#ifdef NO_DUPLICATES_IN_RW_SETS
  if (stm_has_read(tx, addr) != NULL)
    return value;
#endif /* NO_DUPLICATES_IN_RW_SETS */
  stm_add_to_rs(tx, addr
#if DETECTION == TIME_BASED
    , lock, version
#endif /* DETECTION == TIME_BASED */
#ifdef READ_SET_TAGGED
    , tag
#endif /* READ_SET_TAGGED */
#if READ_SET_SOURCE
    , w ? WRITE_FROM_POINTER(tx, w) : STM_INVALID_WRITE
#endif /* READ_SET_SOURCE */
  );
return_value:
  return value;
}

#if DESIGN == WRITE_BACK_ETL_VR
/*
 * Load a word-sized value (visible read).
 */
static INLINE stm_word_t
stm_wbetl_read_visible(stm_tx_t *tx, const stm_word_t *addr)
{
  const stm_lock_t *lock;
  stm_version_t l, l2;
  stm_word_t t value;
  stm_version_t version;
  w_entry_unique_t *wu = NULL;
  stm_tx_policy_t decision;

  PRINT_DEBUG2("==> stm_wbetl_read_visible(t=%p[%lu],a=%p)\n", tx, (unsigned long)tx->end, addr);

  if (GET_STATUS(tx->status) == TX_KILLING) {
    stm_rollback(tx, STM_ABORT_KILLED);
    return 0;
  }

  /* Get reference to lock */
  lock = GET_LOCK(addr);

  /* Try to acquire lock */
restart:
  l = LOCK_READ_ACQ(lock);
restart_no_load:
  if (LOCK_GET_OWNED(addr, l)) {
    /* Locked */
# ifdef UNIT_TX
    if (l == LOCK_UNIT) {
      /* Data modified by a unit store: should not last long => retry */
      goto restart;
    }
# endif /* UNIT_TX */
    /* Do we own the lock? */
    wu = (w_entry_unique_t *)LOCK_GET_ADDR(l);
    /* Simply check if address falls inside our write set (avoids non-faulting load) */
    if (WRITE_UNIQUE_POINTER_VALID(tx, wu)) {
      /* Yes: is it only read-locked? */
      if (!LOCK_GET_WRITE(addr, l)) {
        /* Yes: get value from memory */
        value = ATOMIC_LOAD(addr);
      } else {
        /* No: did we previously write the same address? */
        while (1) {
          if (addr == wu->addr) {
            /* Yes: get value from write set (or from memory if mask was empty) */
            value = (wu->latest->mask == 0 ? ATOMIC_LOAD(addr) : wu->latest->value);
            break;
          }
          if (w->next == NULL) {
            /* No: get value from memory */
            value = ATOMIC_LOAD(addr);
            break;
          }
          wu = POINTER_FROM_WRITE_UNIQUE(tx, wu->next);
        }
      }
      if (GET_STATUS(tx->status) == TX_KILLING) {
        stm_rollback(tx, STM_ABORT_KILLED);
        return 0;
      }
      /* No need to add to read set (will remain valid) */
      return value;
    }
    /* Conflict: CM kicks in */
# if defined(IRREVOCABLE_ENABLED) && defined(IRREVOCABLE_IMPROVED)
    if (tx->irrevocable && ATOMIC_LOAD(&_tinystm.irrevocable) == 1)
      ATOMIC_STORE(&_tinystm.irrevocable, 2);
# endif /* defined(IRREVOCABLE_ENABLED) && defined(IRREVOCABLE_IMPROVED) */
    t = wu->tx->status;
    l2 = LOCK_READ_ACQ(lock);
    if (l != l2) {
      l = l2;
      goto restart_no_load;
    }
    if (t != wu->tx->status) {
      /* Transaction status has changed: restart the whole procedure */
      goto restart;
    }
    tx_conflict_t conflict = {
      .entries.type = LOCK_GET_WRITE(addr, l) ? STM_WR_CONFLICT : STM_RR_CONFLICT,
      .entries.e1 = ENTRY_FROM_WRITE(tx, wu->latest),
      .entries.e2 = ENTRY_INVALID,
# ifdef CONFLICT_TRACKING
      .other = wu->tx,
      .status = t,
# endif /* CONFLICT_TRACKING */
# ifdef CONTENDED_LOCK_TRACKING
      .lock = lock,
# endif /* CONTENDED_LOCK_TRACKING */
    };
    if (GET_STATUS(t) == TX_KILLING) {
      /* We can safely steal lock */
      decision = STM_KILL_OTHER;
    } else {
      decision =
# ifdef IRREVOCABLE_ENABLED
        GET_STATUS(tx->status) == TX_IRREVOCABLE ? STM_KILL_OTHER :
# endif /* IRREVOCABLE_ENABLED */
        stm_conflict_get_decision(tx, &conflict);
      /* Handle STM_KILL_OTHER immediately */
      decision = stm_decision_kill_other(tx, &conflict, decision);
    }

    if (decision == STM_KILL_OTHER) {
      version = wu->version;
      goto acquire;
    }
    decision = stm_decision_implement(tx, &conflict, decision);
    switch (decision) {
      case STM_RETRY:
        goto restart;
      break;
      default:
        assert(decision == STM_KILL_SELF);
        stm_rollback(tx, conflict.entries.type);
        return 0;
      break;
    }
  }
  /* Not locked */
  version = LOCK_GET_TIMESTAMP(l);
acquire:
  /* Acquire lock (ETL) */

  /* Add address to unique write set */
  assert(!wu || !WRITE_UNIQUE_POINTER_VALID(tx, wu));
  wu = stm_add_to_ws_unique(tx, addr);

  if (tx->w_set.nb_entries == tx->w_set.size)
    stm_rollback(tx, STM_ABORT_EXTEND_WS);
  w = &tx->w_set.entries[tx->w_set.nb_entries];
  value = ATOMIC_LOAD(addr);
  if (LOCK_WRITE_CAS(lock, l, LOCK_SET_ADDR_READ((stm_word_t)wu)) == 0) {
    --tx->w_set_unique.nb_entries;
    goto restart;
  }
  /* Add entry to write set */
  w->mask = 0;
  w->value = value;
#if OPERATION_LOGGING != OPLOG_NONE
  w->op = int_stm_get_log(tx);
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  w->unique = WRITE_UNIQUE_FROM_POINTER(tx, wu);
#if DETECTION == TIME_BASED
  wu->version = version;
#endif /* DETECTION == TIME_BASED */
  wu->next = STM_INVALID_WRITE_UNIQUE;
  tx->w_set.nb_entries++;

  wu->latest = WRITE_FROM_POINTER(tx, w);
  return value;
}
#endif /* DESIGN == WRITE_BACK_ETL_VR */

static INLINE stm_word_t
stm_wbetl_read(stm_tx_t *tx, const stm_word_t *addr
#ifdef READ_SET_TAGGED
  , uintptr_t tag
#endif /* READ_SET_TAGGED */
  )
{
#if DESIGN == WRITE_BACK_ETL_VR
  if (unlikely((tx->attr.visible_reads))) {
    /* Use visible read */
    return stm_wbetl_read_visible(tx, addr
#ifdef READ_SET_TAGGED
      , tag
#endif /* READ_SET_TAGGED */
    );
  }
#endif /* DESIGN == WRITE_BACK_ETL_VR */
  return stm_wbetl_read_invisible(tx, addr
#ifdef READ_SET_TAGGED
    , tag
#endif /* READ_SET_TAGGED */
  );
}

static INLINE w_entry_t *
stm_wbetl_write(stm_tx_t *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
  const stm_lock_t *lock;
  stm_version_t l;
#if DETECTION == TIME_BASED
  stm_version_t version;
  r_entry_t *r;
#endif /* DETECTION == TIME_BASED */
  w_entry_t *w;
  w_entry_unique_t *wu = NULL, *prev = NULL;
#ifdef TRANSACTION_OPERATIONS
  stm_version_t l2;
  stm_word_t t;
#endif /* TRANSACTION_OPERATIONS */
  tx_conflict_t conflict;
  stm_tx_policy_t decision;

  PRINT_DEBUG2("==> stm_wbetl_write(t=%p[%lu],a=%p,d=%p-%lu,m=0x%lx)\n",
               tx, (unsigned long)tx->end, addr, (void *)value, (unsigned long)value, (unsigned long)mask);

  /* Get reference to lock */
  lock = GET_LOCK(addr);

  /* Try to acquire lock */
restart:
  l = LOCK_READ_ACQ(lock);
restart_no_load:
  if (unlikely(LOCK_GET_OWNED(addr, l))) {
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
      /* Yes */
#ifdef TRANSACTION_OPERATIONS
      /* If read-locked: upgrade lock */
      if (!LOCK_GET_WRITE(addr, l)) {
        if (LOCK_WRITE_CAS(lock, l, LOCK_UPGRADE(l)) == 0) {
          /* Lock must have been stolen: abort */
          stm_rollback(tx, STM_ABORT_KILLED);
          return NULL;
        }
        tx->w_set.has_writes++;
      }
#endif /* TRANSACTION_OPERATIONS */
      if (mask == 0) {
        /* No need to insert new entry or modify existing one */
        return POINTER_FROM_WRITE(tx, wu->latest);
      }
      prev = wu;
      /* Did we previously write the same address? */
      while (1) {
        if (addr == prev->addr) {
          w = POINTER_FROM_WRITE(tx, prev->latest);
          /* No need to add to write set */
          if (mask != ~(stm_word_t)0) {
            if (w->mask == 0)
              w->value = ATOMIC_LOAD(addr);
            value = (w->value & ~mask) | (value & mask);
          }
          w->value = value;
          w->mask |= mask;
          return POINTER_FROM_WRITE(tx, prev->latest);
        }
        if (!WRITE_UNIQUE_VALID(tx, prev->next)) {
          /* Remember last entry in linked list (for adding new entry) */
          break;
        }
        prev = POINTER_FROM_WRITE_UNIQUE(tx, prev->next);
      }
#if DETECTION == TIME_BASED
      /* Get version from previous write set entry (all entries in linked list have same version) */
      version = prev->version;
#endif /* DETECTION == TIME_BASED */
      /* Must add to write set */
      wu = stm_add_to_ws_unique(tx, addr);
      if (tx->w_set.nb_entries == tx->w_set.size)
        stm_rollback(tx, STM_ABORT_EXTEND_WS);
      w = &tx->w_set.entries[tx->w_set.nb_entries];
      goto do_write;
    }
    /* Conflict: CM kicks in */
#if defined(IRREVOCABLE_ENABLED) && defined(IRREVOCABLE_IMPROVED)
    if (tx->irrevocable && ATOMIC_LOAD(&_tinystm.irrevocable) == 1)
      ATOMIC_STORE(&_tinystm.irrevocable, 2);
#endif /* defined(IRREVOCABLE_ENABLED) && defined(IRREVOCABLE_IMPROVED) */
#ifdef IRREVOCABLE_ENABLED
    if (tx->irrevocable) {
      /* Spin while locked */
      goto restart;
    }
#endif /* IRREVOCABLE_ENABLED */
#ifdef TRANSACTION_OPERATIONS
    t = wu->tx->status;
    l2 = LOCK_READ_ACQ(lock);
    if (l != l2) {
      l = l2;
      goto restart_no_load;
    }
    if (t != wu->tx->status) {
      /* Transaction status has changed: restart the whole procedure */
      goto restart;
    }
    conflict.entries.type = STM_WW_CONFLICT;
    conflict.entries.e1 = ENTRY_FROM_WRITE(tx, wu->latest);
    conflict.entries.e2 = ENTRY_INVALID;
# ifdef CONFLICT_TRACKING
    conflict.other = NULL;
    conflict.status = 0;
# endif /* CONFLICT_TRACKING */
# ifdef CONTENDED_LOCK_TRACKING
    conflict.lock = lock;
# endif /* CONTENDED_LOCK_TRACKING */
    if (GET_STATUS(t) == TX_KILLING) {
      /* We can safely steal lock */
      decision = STM_KILL_OTHER;
    } else {
      decision =
# ifdef IRREVOCABLE_ENABLED
        GET_STATUS(tx->status) == TX_IRREVOCABLE ? STM_KILL_OTHER :
# endif /* IRREVOCABLE_ENABLED */
        stm_conflict_get_decision(tx, &conflict);
      /* Handle STM_KILL_OTHER immediately */
      decision = stm_decision_kill_other(tx, &conflict, decision);
    }

    if (decision == STM_KILL_OTHER) {
      /* Handle write after reads (before CAS) */
      version = wu->version;
      goto acquire;
    }
#else /* TRANSACTION_OPERATIONS */
    conflict.entries.type = STM_WW_CONFLICT;
    conflict.entries.e1 = ENTRY_FROM_WRITE(tx, wu->latest);
    conflict.entries.e2 = ENTRY_INVALID;
# ifdef CONFLICT_TRACKING
    conflict.other = NULL;
    conflict.status = 0;
# endif /* CONFLICT_TRACKING */
# ifdef CONTENDED_LOCK_TRACKING
    conflict.lock = lock;
# endif /* CONTENDED_LOCK_TRACKING */
    decision = stm_conflict_get_decision(tx, &conflict);
#endif /* TRANSACTION_OPERATIONS */
    decision = stm_decision_implement(tx, &conflict, decision);
    switch (decision) {
      case STM_RETRY:
        goto restart;
      break;
      default:
        assert(decision == STM_KILL_SELF);
        stm_rollback(tx, conflict.entries.type);
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
  if (unlikely(tx->irrevocable))
    goto acquire_no_check;
#endif /* IRREVOCABLE_ENABLED */
acquire:
#if DETECTION == TIME_BASED
  if (unlikely(version > tx->end)) {
    /* We might have read an older version previously */
# ifdef UNIT_TX
    if (unlikely(tx->attr.no_extend)) {
      stm_rollback(tx, STM_ABORT_VAL_WRITE);
      return NULL;
    }
# endif /* UNIT_TX */
    if (unlikely((r = stm_has_read(tx, addr)) != NULL)) {
      /* Read version must be older (otherwise, tx->end >= version) */
      /* Not much we can do: abort */
# if DESIGN == WRITE_BACK_ETL_VR
      /* Abort caused by invisible reads */
      tx->visible_reads++;
# endif /* DESIGN == WRITE_BACK_ETL_VR */
      conflict.entries.type = STM_WR_VALIDATE;
      conflict.entries.e1 = ENTRY_FROM_READ_POINTER(tx, r);
      conflict.entries.e2 = wu ? ENTRY_FROM_WRITE(tx, wu->latest) : ENTRY_INVALID;
# ifdef CONFLICT_TRACKING
      conflict.other = tx;
      conflict.status = t;
# endif /* CONFLICT_TRACKING */
# ifdef CONTENDED_LOCK_TRACKING
      conflict.lock = lock;
# endif /* CONTENDED_LOCK_TRACKING */
      decision = stm_conflict_handle_all(tx, &conflict);
      switch (decision) {
        case STM_RETRY:
          goto restart;
        break;
        default:
          assert(decision == STM_KILL_SELF);
          return NULL;
        break;
      }
    }
  }
#endif /* DETECTION == TIME_BASED */

  /* Acquire lock (ETL) */
acquire_no_check:
  /* Add address to unique write set */
  assert(!wu || !WRITE_UNIQUE_POINTER_VALID(tx, wu));
  wu = stm_add_to_ws_unique(tx, addr);

  if (unlikely(tx->w_set.nb_entries == tx->w_set.size))
    stm_allocate_ws_entries(tx, 1);
  w = &tx->w_set.entries[tx->w_set.nb_entries];
  if (unlikely(LOCK_WRITE_CAS(lock, l, LOCK_SET_ADDR_WRITE(wu, l)) == 0)) {
    --tx->w_set_unique.nb_entries;
    goto restart;
  }
  /* We own the lock here (ETL) */
do_write:
  /* Add address to write set */
  w->mask = mask;
  if (unlikely(mask == 0)) {
    /* Do not write anything */
#ifndef NDEBUG
    w->value = 0;
#endif /* ! NDEBUG */
  } else {
    /* Remember new value */
    if (mask != ~(stm_word_t)0)
      value = (ATOMIC_LOAD(addr) & ~mask) | (value & mask);
    w->value = value;
  }
#if OPERATION_LOGGING != OPLOG_NONE
  w->op = int_stm_get_log(tx);
#endif /* OPERATION_LOGGING != OPLOG_NONE */
  w->unique = WRITE_UNIQUE_FROM_POINTER(tx, wu);
#if DETECTION == TIME_BASED
  wu->version = version;
#endif /* DETECTION == TIME_BASED */
  wu->next = STM_INVALID_WRITE_UNIQUE;
  if (prev != NULL) {
    /* Link new entry in list */
    prev->next = WRITE_UNIQUE_FROM_POINTER(tx, wu);
  }
  tx->w_set.nb_entries++;
  tx->w_set_unique.has_writes++;

  wu->latest = WRITE_FROM_POINTER(tx, w);
  return w;
}

static INLINE stm_word_t
stm_wbetl_RaR(stm_tx_t *tx, stm_word_t *addr)
{
  /* Possible optimization: avoid adding to read set again */
  return stm_wbetl_read(tx, addr);
}

static INLINE stm_word_t
stm_wbetl_RaW(stm_tx_t *tx, stm_word_t *addr)
{
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

  /* Read directly from write set entry. */
  return POINTER_FROM_WRITE(tx, wu->latest)->value;
}

static INLINE stm_word_t
stm_wbetl_RfW(stm_tx_t *tx, stm_word_t *addr)
{
  /* Acquire lock as write. */
  stm_wbetl_write(tx, addr, 0, 0);
  /* Now the lock is owned, read directly from memory is safe. */
  /* TODO Unsafe with CM_MODULAR */
  return *addr;
}

static INLINE void
stm_wbetl_WaR(stm_tx_t *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
  /* Probably no optimization can be done here. */
  stm_wbetl_write(tx, addr, value, mask);
}

static INLINE void
stm_wbetl_WaW(stm_tx_t *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
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
  while (1) {
    if (addr == wu->addr) {
      w_entry_t *w = POINTER_FROM_WRITE(tx, wu->latest);
      /* No need to add to write set */
      if (mask != ~(stm_word_t)0) {
        if (w->mask == 0)
          w->value = ATOMIC_LOAD(addr);
        value = (w->value & ~mask) | (value & mask);
      }
      w->value = value;
      w->mask |= mask;
      return;
    }
    /* The entry must exist */
    assert (WRITE_UNIQUE_VALID(tx, wu->next));
    assert (wu != POINTER_FROM_WRITE_UNIQUE(tx, wu->next));
    wu = POINTER_FROM_WRITE_UNIQUE(tx, wu->next);
  }
}

static INLINE int
stm_wbetl_commit(stm_tx_t *tx)
{
#if DETECTION == TIME_BASED || defined(IRREVOCABLE_IMPROVED)
  stm_version_t t;
#endif /* DETECTION == TIME_BASED || IRREVOCABLE_IMPROVE */

  PRINT_DEBUG("==> stm_wbetl_commit(%p[%lu])\n", tx, (unsigned long)tx->end);

  /* A read-only transaction with visible reads must simply drop locks */
  /* FIXME: if killed? */
  if (tx->w_set_unique.has_writes == 0) {
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
    for (const w_entry_unique_t *wu = tx->w_set_unique.entries + WRITE_RESERVED_IDX + 1; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#else
    for (const w_entry_unique_t *wu = tx->w_set_unique.entries; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
    {
      /* Only drop lock for last covered address in write set */
      if (!WRITE_UNIQUE_VALID(tx, wu->next)) {
        assert(LOCK_GET_OWNED(wu->addr, LOCK_READ_ACQ(wu->lock)) && WRITE_UNIQUE_POINTER_VALID(tx, (w_entry_unique_t *)LOCK_GET_ADDR(LOCK_READ_ACQ(wu->lock))) && ((w_entry_unique_t *)(LOCK_GET_ADDR(LOCK_READ_ACQ(wu->lock))))->lock == wu->lock);
#if DETECTION == TIME_BASED
        LOCK_WRITE_REL(wu->lock, LOCK_SET_TIMESTAMP(wu, wu->version, LOCK_READ_ACQ(wu->lock)));
#endif /* DETECTION */
      }
    }
    /* Update clock so that future transactions get higher timestamp (liveness of timestamp CM) */
    FETCH_INC_CLOCK;
    goto end;
  }

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
      unlikely(tx->end != t - 1 && !stm_wbetl_validate(tx))
#endif /* DETECTION */
  ) {
    /* Cannot commit */
#if DESIGN == WRITE_BACK_ETL_VR
    /* Abort caused by invisible reads */
    tx->visible_reads++;
#endif /* DESIGN == WRITE_BACK_ETL_VR */
    stm_rollback(tx, STM_ABORT_VAL_COMMIT);
    return 0;
  }

#ifdef IRREVOCABLE_ENABLED
release_locks:
#endif /* IRREVOCABLE_ENABLED */

  /* Install new versions, drop locks and set new timestamp */
#if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
  for (const w_entry_unique_t *wu = tx->w_set_unique.entries + WRITE_RESERVED_IDX + 1; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#else
  for (const w_entry_unique_t *wu = tx->w_set_unique.entries; WRITE_UNIQUE_POINTER_VALID(tx, wu); ++wu)
#endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
  {
    w_entry_t *w = POINTER_FROM_WRITE(tx, wu->latest);
    if (w->mask != 0)
      ATOMIC_STORE(wu->addr, w->value);
    /* Only drop lock for last covered address in write set */
    if (!WRITE_UNIQUE_VALID(tx, wu->next)) {
      /* In case of visible read, reset lock to its previous timestamp */
      assert(LOCK_GET_OWNED(wu->addr, LOCK_READ_ACQ(wu->lock)) && WRITE_UNIQUE_POINTER_VALID(tx, (w_entry_unique_t *)LOCK_GET_ADDR(LOCK_READ_ACQ(wu->lock))) && ((w_entry_unique_t *)(LOCK_GET_ADDR(LOCK_READ_ACQ(wu->lock))))->lock == wu->lock);
restart:
      if (w->mask == 0) {
#if DETECTION == TIME_BASED
        LOCK_WRITE_REL(wu->lock, LOCK_SET_TIMESTAMP(wu, wu->version, LOCK_READ_ACQ(wu->lock)));
#endif /* DETECTION */
      } else {
#if DETECTION == TIME_BASED
        LOCK_WRITE_REL(wu->lock, LOCK_SET_TIMESTAMP(wu, t, LOCK_READ_ACQ(wu->lock)));
#endif /* DETECTION */
      }
    }
  }

end:
  return 1;
}

#endif /* _STM_WBETL_H_ */

