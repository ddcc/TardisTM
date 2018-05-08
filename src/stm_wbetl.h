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
  int i;
  stm_version_t l;

  PRINT_DEBUG("==> stm_wbetl_validate(%p[%lu-%lu])\n", tx, (unsigned long)tx->start, (unsigned long)tx->end);

  /* Validate reads */
  r = tx->r_set.entries;
  for (i = tx->r_set.nb_entries; i > 0; i--, r++) {
    /* Read lock */
    l = LOCK_READ_ACQ(r->lock);
    /* Unlocked and still the same version? */
    if (LOCK_GET_OWNED(l)) {
      /* Do we own the lock? */
      w_entry_t *w = (w_entry_t *)LOCK_GET_ADDR(l);
      /* Simply check if address falls inside our write set (avoids non-faulting load) */
      if (!(tx->w_set.entries <= w && w < tx->w_set.entries + tx->w_set.nb_entries))
      {
        /* Locked by another transaction: cannot validate */
#ifdef CONFLICT_TRACKING
        if (_tinystm.conflict_cb != NULL) {
# ifdef UNIT_TX
          if (l != LOCK_UNIT) {
# endif /* UNIT_TX */
            /* Call conflict callback */
            _tinystm.conflict_cb(tx, w->tx, STM_RD_VALIDATE, ENTRY_FROM_READ(r), ENTRY_FROM_WRITE(w));
# ifdef UNIT_TX
          }
# endif /* UNIT_TX */
        }
#endif /* CONFLICT_TRACKING */
        return 0;
      }
      /* We own the lock: OK */
    } else {
      if (LOCK_GET_TIMESTAMP(l) != r->version) {
#ifdef CONFLICT_TRACKING
        if (_tinystm.conflict_cb != NULL) {
          /* Call conflict callback */
          _tinystm.conflict_cb(tx, NULL, STM_RD_VALIDATE, ENTRY_FROM_READ(r), 0);
        }
#endif /* CONFLICT_TRACKING */
        /* Other version: cannot validate */
        return 0;
      }
      /* Same version: OK */
    }
  }
  return 1;
}

/*
 * Extend snapshot range.
 */
static INLINE int
stm_wbetl_extend(stm_tx_t *tx)
{
  stm_version_t now;

  PRINT_DEBUG("==> stm_wbetl_extend(%p[%lu-%lu])\n", tx, (unsigned long)tx->start, (unsigned long)tx->end);

#ifdef UNIT_TX
  /* Extension is disabled */
  if (tx->attr.no_extend)
    return 0;
#endif /* UNIT_TX */

  /* Get current time */
  now = GET_CLOCK;
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
  w_entry_t *w;
  int i;
#ifdef TRANSACTION_OPERATIONS
  stm_word_t t;
#endif /* TRANSACTION_OPERATIONS */
#if CM == CM_BACKOFF
  unsigned long wait;
  volatile int j;
#endif /* CM == CM_BACKOFF */

  PRINT_DEBUG("==> stm_wbetl_rollback(%p[%lu-%lu])\n", tx, (unsigned long)tx->start, (unsigned long)tx->end);

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
  i = tx->w_set.nb_entries;
  if (i > 0) {
    w = tx->w_set.entries;
    for (; i > 0; i--, w++) {
      if (w->next == NULL) {
        /* Only drop lock for last covered address in write set */
        LOCK_WRITE(w->lock, LOCK_SET_TIMESTAMP(w->version));
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
stm_wbetl_read_invisible(stm_tx_t *tx, volatile stm_word_t *addr)
{
  const stm_lock_t *lock;
  stm_version_t l, l2;
  stm_word_t value;
  stm_version_t version;
  w_entry_t *w;
#ifdef TRANSACTION_OPERATIONS
  stm_word_t t;
  stm_tx_policy_t decision;
#endif /* TRANSACTION_OPERATIONS */

  PRINT_DEBUG2("==> stm_wbetl_read_invisible(t=%p[%lu-%lu],a=%p)\n", tx, (unsigned long)tx->start, (unsigned long)tx->end, addr);

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
  if (unlikely(LOCK_GET_WRITE(l))) {
    /* Locked */
    /* Do we own the lock? */
    w = (w_entry_t *)LOCK_GET_ADDR(l);
    /* Simply check if address falls inside our write set (avoids non-faulting load) */
    if (likely(tx->w_set.entries <= w && w < tx->w_set.entries + tx->w_set.nb_entries)) {
      /* Yes: did we previously write the same address? */
      while (1) {
        if (addr == w->addr) {
          /* Yes: get value from write set (or from memory if mask was empty) */
          value = (w->mask == 0 ? ATOMIC_LOAD(addr) : w->value);
          break;
        }
        if (w->next == NULL) {
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
        w = w->next;
      }
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
#ifdef IRREVOCABLE_ENABLED
    if (unlikely(tx->irrevocable)) {
      /* Spin while locked */
      goto restart;
    }
#endif /* IRREVOCABLE_ENABLED */
#ifdef TRANSACTION_OPERATIONS
    t = w->tx->status;
    l2 = LOCK_READ_ACQ(lock);
    if (l != l2) {
      l = l2;
      goto restart_no_load;
    }
    if (t != w->tx->status) {
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
      version = ATOMIC_LOAD(&w->version);
      /* Read data */
      value = ATOMIC_LOAD(addr);
      /* Check that data has not been written */
      if (t != w->tx->status) {
        /* Data concurrently modified: a new version might be available => retry */
        goto restart;
      }
      if (version >= tx->start && (version <= tx->end || (!tx->attr.read_only && stm_wbetl_extend(tx)))) {
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
      decision =
# ifdef IRREVOCABLE_ENABLED
        GET_STATUS(tx->status) == TX_IRREVOCABLE ? STM_KILL_OTHER :
# endif /* IRREVOCABLE_ENABLED */
# ifdef CONFLICT_TRACKING
        _tinystm.conflict_cb != NULL ? _tinystm.conflict_cb(tx, w->tx, STM_RW_CONFLICT, ENTRY_FROM_WRITE(w), 0) :
# endif /* CONFLICT_TRACKING */
        STM_KILL_SELF;
      if (decision == STM_KILL_OTHER) {
        /* Kill other */
        if (!stm_kill(tx, w->tx, t)) {
          /* Transaction may have committed or aborted: retry */
          goto restart;
        }
      }
    }
    if (decision == STM_KILL_OTHER) {
      /* Steal lock */
      l2 = LOCK_SET_TIMESTAMP(w->version);
      if (LOCK_WRITE_CAS(lock, l, l2) == 0)
        goto restart;
      l = l2;
      goto restart_no_load;
    }
    /* Kill self */
#endif /* TRANSACTION_OPERATIONS */
#ifdef CONTENDED_LOCK_TRACKING
    if ((decision & STM_DELAY) != 0)
      tx->c_lock = lock;
#endif /* CONTENDED_LOCK_TRACKING */
    /* Abort */
    stm_rollback(tx, STM_ABORT_RW_CONFLICT);
    return 0;
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
    /* Check timestamp */
#ifdef TRANSACTION_OPERATIONS
    if (LOCK_GET_READ(l))
      version = ((w_entry_t *)LOCK_GET_ADDR(l))->version;
    else
      version = LOCK_GET_TIMESTAMP(l);
#else
    version = LOCK_GET_TIMESTAMP(l);
#endif /* TRANSACTION_OPERATIONS */
    /* Valid version? */
    if (unlikely(version > tx->end)) {
      /* No: try to extend first (except for read-only transactions: no read set) */
      if (tx->attr.read_only || !stm_wbetl_extend(tx)) {
        /* Not much we can do: abort */
#if DESIGN == WRITE_BACK_ETL_VR
        /* Abort caused by invisible reads */
        tx->visible_reads++;
#endif /* DESIGN == WRITE_BACK_ETL_VR */
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
#ifdef TRANSACTION_OPERATIONS
    /* Check if killed (necessary to avoid possible race on read-after-write) */
    if (GET_STATUS(tx->status) == TX_KILLING) {
      stm_rollback(tx, STM_ABORT_KILLED);
      return 0;
    }
#endif /* TRANSACTION_OPERATIONS */
  }
  /* We have a good version: add to read set (update transactions) and return value */

#ifdef READ_LOCKED_DATA
 add_to_read_set:
#endif /* READ_LOCKED_DATA */
  stm_add_to_rs(tx, lock, version);
 return_value:
  return value;
}

#if DESIGN == WRITE_BACK_ETL_VR
/*
 * Load a word-sized value (visible read).
 */
static INLINE stm_word_t
stm_wbetl_read_visible(stm_tx_t *tx, volatile stm_word_t *addr)
{
  const stm_lock_t *lock;
  stm_version_t l, l2;
  stm_word_t t value;
  stm_version_t version;
  w_entry_t *w;
  stm_tx_policy_t decision;

  PRINT_DEBUG2("==> stm_wbetl_read_visible(t=%p[%lu-%lu],a=%p)\n", tx, (unsigned long)tx->start, (unsigned long)tx->end, addr);

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
  if (LOCK_GET_OWNED(l)) {
    /* Locked */
# ifdef UNIT_TX
    if (l == LOCK_UNIT) {
      /* Data modified by a unit store: should not last long => retry */
      goto restart;
    }
# endif /* UNIT_TX */
    /* Do we own the lock? */
    w = (w_entry_t *)LOCK_GET_ADDR(l);
    /* Simply check if address falls inside our write set (avoids non-faulting load) */
    if (tx->w_set.entries <= w && w < tx->w_set.entries + tx->w_set.nb_entries) {
      /* Yes: is it only read-locked? */
      if (!LOCK_GET_WRITE(l)) {
        /* Yes: get value from memory */
        value = ATOMIC_LOAD(addr);
      } else {
        /* No: did we previously write the same address? */
        while (1) {
          if (addr == w->addr) {
            /* Yes: get value from write set (or from memory if mask was empty) */
            value = (w->mask == 0 ? ATOMIC_LOAD(addr) : w->value);
            break;
          }
          if (w->next == NULL) {
            /* No: get value from memory */
            value = ATOMIC_LOAD(addr);
            break;
          }
          w = w->next;
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
    t = w->tx->status;
    l2 = LOCK_READ_ACQ(lock);
    if (l != l2) {
      l = l2;
      goto restart_no_load;
    }
    if (t != w->tx->status) {
      /* Transaction status has changed: restart the whole procedure */
      goto restart;
    }
    if (GET_STATUS(t) == TX_KILLING) {
      /* We can safely steal lock */
      decision = STM_KILL_OTHER;
    } else {
      decision =
# ifdef IRREVOCABLE_ENABLED
        GET_STATUS(tx->status) == TX_IRREVOCABLE ? STM_KILL_OTHER :
# endif /* IRREVOCABLE_ENABLED */
# ifdef CONFLICT_TRACKING
        _tinystm.conflict_cb != NULL ? _tinystm.conflict_cb(tx, w->tx, (LOCK_GET_WRITE(l) ? STM_WR_CONFLICT : STM_RR_CONFLICT), ENTRY_FROM_WRITE(w), 0) :
# endif /* CONFLICT_TRACKING */
        STM_KILL_SELF;
      if (decision == STM_KILL_OTHER) {
        /* Kill other */
        if (!stm_kill(tx, w->tx, t)) {
          /* Transaction may have committed or aborted: retry */
          goto restart;
        }
      }
    }
    if (decision == STM_KILL_OTHER) {
      version = w->version;
      goto acquire;
    }
    /* Kill self */
#ifdef CONTENDED_LOCK_TRACKING
    if ((decision & STM_DELAY) != 0)
      tx->c_lock = lock;
#endif /* CONTENDED_LOCK_TRACKING */
    /* Abort */
    stm_rollback(tx, (LOCK_GET_WRITE(l) ? STM_ABORT_WR_CONFLICT : STM_ABORT_RR_CONFLICT));
    return 0;
  }
  /* Not locked */
  version = LOCK_GET_TIMESTAMP(l);
 acquire:
  /* Acquire lock (ETL) */
  if (tx->w_set.nb_entries == tx->w_set.size)
    stm_rollback(tx, STM_ABORT_EXTEND_WS);
  w = &tx->w_set.entries[tx->w_set.nb_entries];
  w->version = version;
  value = ATOMIC_LOAD(addr);
  if (ATOMIC_CAS_FULL(lock, l, LOCK_SET_ADDR_READ((stm_word_t)w)) == 0)
    goto restart;
  /* Add entry to write set */
  w->addr = addr;
  w->mask = 0;
  w->lock = lock;
  w->value = value;
  w->next = NULL;
  tx->w_set.nb_entries++;
  return value;
}
#endif /* DESIGN == WRITE_BACK_ETL_VR */

static INLINE stm_word_t
stm_wbetl_read(stm_tx_t *tx, volatile stm_word_t *addr)
{
#if DESIGN == WRITE_BACK_ETL_VR
  if (unlikely((tx->attr.visible_reads))) {
    /* Use visible read */
    return stm_wbetl_read_visible(tx, addr);
  }
#endif /* DESIGN == WRITE_BACK_ETL_VR */
  return stm_wbetl_read_invisible(tx, addr);
}

static INLINE w_entry_t *
stm_wbetl_write(stm_tx_t *tx, volatile stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
  const stm_lock_t *lock;
  stm_version_t l;
  stm_version_t version;
  r_entry_t *r;
  w_entry_t *w, *prev = NULL;
#ifdef TRANSACTION_OPERATIONS
  stm_version_t l2;
  stm_word_t t;
  stm_tx_policy_t decision;
#endif /* TRANSACTION_OPERATIONS */

  PRINT_DEBUG2("==> stm_wbetl_write(t=%p[%lu-%lu],a=%p,d=%p-%lu,m=0x%lx)\n",
               tx, (unsigned long)tx->start, (unsigned long)tx->end, addr, (void *)value, (unsigned long)value, (unsigned long)mask);

  /* Get reference to lock */
  lock = GET_LOCK(addr);

  /* Try to acquire lock */
 restart:
  l = LOCK_READ_ACQ(lock);
 restart_no_load:
  if (unlikely(LOCK_GET_OWNED(l))) {
    /* Locked */

#ifdef UNIT_TX
    if (l == LOCK_UNIT) {
      /* Data modified by a unit store: should not last long => retry */
      goto restart;
    }
#endif /* UNIT_TX */

    /* Do we own the lock? */
    w = (w_entry_t *)LOCK_GET_ADDR(l);
    /* Simply check if address falls inside our write set (avoids non-faulting load) */
    if (likely(tx->w_set.entries <= w && w < tx->w_set.entries + tx->w_set.nb_entries)) {
      /* Yes */
#ifdef TRANSACTION_OPERATIONS
      /* If read-locked: upgrade lock */
      if (!LOCK_GET_WRITE(l)) {
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
        return w;
      }
      prev = w;
      /* Did we previously write the same address? */
      while (1) {
        if (addr == prev->addr) {
          /* No need to add to write set */
          if (mask != ~(stm_word_t)0) {
            if (prev->mask == 0)
              prev->value = ATOMIC_LOAD(addr);
            value = (prev->value & ~mask) | (value & mask);
          }
          prev->value = value;
          prev->mask |= mask;
          return prev;
        }
        if (prev->next == NULL) {
          /* Remember last entry in linked list (for adding new entry) */
          break;
        }
        prev = prev->next;
      }
      /* Get version from previous write set entry (all entries in linked list have same version) */
      version = prev->version;
      /* Must add to write set */
      if (tx->w_set.nb_entries == tx->w_set.size)
        stm_rollback(tx, STM_ABORT_EXTEND_WS);
      w = &tx->w_set.entries[tx->w_set.nb_entries];
      w->version = version;
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
    t = w->tx->status;
    l2 = LOCK_READ_ACQ(lock);
    if (l != l2) {
      l = l2;
      goto restart_no_load;
    }
    if (t != w->tx->status) {
      /* Transaction status has changed: restart the whole procedure */
      goto restart;
    }
    if (GET_STATUS(t) == TX_KILLING) {
      /* We can safely steal lock */
      decision = STM_KILL_OTHER;
    } else {
      decision =
# ifdef IRREVOCABLE_ENABLED
        GET_STATUS(tx->status) == TX_IRREVOCABLE ? STM_KILL_OTHER :
# endif /* IRREVOCABLE_ENABLED */
# ifdef CONFLICT_TRACKING
        _tinystm.conflict_cb != NULL ? _tinystm.conflict_cb(tx, w->tx, STM_WW_CONFLICT, ENTRY_FROM_WRITE(w), 0) :
# endif /* CONFLICT_TRACKING */
        STM_KILL_SELF;
      if (decision == STM_KILL_OTHER) {
        /* Kill other */
        if (!stm_kill(tx, w->tx, t)) {
          /* Transaction may have committed or aborted: retry */
          goto restart;
        }
      }
    }
    if (decision == STM_KILL_OTHER) {
      /* Handle write after reads (before CAS) */
      version = w->version;
      goto acquire;
    }
#endif /* TRANSACTION_OPERATIONS */
    /* Kill self */
#ifdef CONTENDED_LOCK_TRACKING
    if ((decision & STM_DELAY) != 0)
      tx->c_lock = lock;
#endif /* CONTENDED_LOCK_TRACKING */
    /* Abort */
    stm_rollback(tx, STM_ABORT_WW_CONFLICT);
    return NULL;
  }
  /* Not locked */
  /* Handle write after reads (before CAS) */
  version = LOCK_GET_TIMESTAMP(l);
#ifdef IRREVOCABLE_ENABLED
  /* In irrevocable mode, no need to revalidate */
  if (unlikely(tx->irrevocable))
    goto acquire_no_check;
#endif /* IRREVOCABLE_ENABLED */
 acquire:
  if (unlikely(version > tx->end)) {
    /* We might have read an older version previously */
#ifdef UNIT_TX
    if (unlikely(tx->attr.no_extend)) {
      stm_rollback(tx, STM_ABORT_VAL_WRITE);
      return NULL;
    }
#endif /* UNIT_TX */
    if (unlikely((r = stm_has_read(tx, lock)) != NULL)) {
      /* Read version must be older (otherwise, tx->end >= version) */
      /* Not much we can do: abort */
#if DESIGN == WRITE_BACK_ETL_VR
      /* Abort caused by invisible reads */
      tx->visible_reads++;
#endif /* DESIGN == WRITE_BACK_ETL_VR */
#ifdef CONFLICT_TRACKING
      if (_tinystm.conflict_cb != NULL) {
          /* Call conflict callback */
          _tinystm.conflict_cb(tx, NULL, STM_WR_VALIDATE, ENTRY_FROM_READ(r), 0);
      }
#endif /* CONFLICT_TRACKING */
      stm_rollback(tx, STM_ABORT_VAL_WRITE);
      return NULL;
    }
  }
  /* Acquire lock (ETL) */
#ifdef IRREVOCABLE_ENABLED
 acquire_no_check:
#endif /* IRREVOCABLE_ENABLED */
  if (unlikely(tx->w_set.nb_entries == tx->w_set.size))
    stm_rollback(tx, STM_ABORT_EXTEND_WS);
  w = &tx->w_set.entries[tx->w_set.nb_entries];
  w->version = version;
  if (unlikely(LOCK_WRITE_CAS(lock, l, LOCK_SET_ADDR_WRITE((stm_word_t)w)) == 0))
    goto restart;
  /* We own the lock here (ETL) */
do_write:
  /* Add address to write set */
  w->addr = addr;
  w->mask = mask;
  w->lock = lock;
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
  w->version = version;
  w->next = NULL;
  if (prev != NULL) {
    /* Link new entry in list */
    prev->next = w;
  }
  tx->w_set.nb_entries++;
  tx->w_set.has_writes++;

  return w;
}

static INLINE stm_word_t
stm_wbetl_RaR(stm_tx_t *tx, volatile stm_word_t *addr)
{
  /* Possible optimization: avoid adding to read set again */
  return stm_wbetl_read(tx, addr);
}

static INLINE stm_word_t
stm_wbetl_RaW(stm_tx_t *tx, volatile stm_word_t *addr)
{
  const stm_lock_t *lock;
  stm_version_t l;
  w_entry_t *w;

  /* Get reference to lock */
  lock = GET_LOCK(addr);

  l = LOCK_READ_ACQ(lock);
  /* Does the lock owned? */
  assert(LOCK_GET_WRITE(l));
  /* Do we own the lock? */
  w = (w_entry_t *)LOCK_GET_ADDR(l);
  assert(tx->w_set.entries <= w && w < tx->w_set.entries + tx->w_set.nb_entries);

  /* Read directly from write set entry. */
  return w->value;
}

static INLINE stm_word_t
stm_wbetl_RfW(stm_tx_t *tx, volatile stm_word_t *addr)
{
  /* Acquire lock as write. */
  stm_wbetl_write(tx, addr, 0, 0);
  /* Now the lock is owned, read directly from memory is safe. */
  /* TODO Unsafe with CM_MODULAR */
  return *addr;
}

static INLINE void
stm_wbetl_WaR(stm_tx_t *tx, volatile stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
  /* Probably no optimization can be done here. */
  stm_wbetl_write(tx, addr, value, mask);
}

static INLINE void
stm_wbetl_WaW(stm_tx_t *tx, volatile stm_word_t *addr, stm_word_t value, stm_word_t mask)
{
  const stm_lock_t *lock;
  stm_version_t l;
  w_entry_t *w;

  /* Get reference to lock */
  lock = GET_LOCK(addr);
  l = LOCK_READ_ACQ(lock);
  /* Does the lock owned? */
  assert(LOCK_GET_WRITE(l));
  /* Do we own the lock? */
  w = (w_entry_t *)LOCK_GET_ADDR(l);
  assert(tx->w_set.entries <= w && w < tx->w_set.entries + tx->w_set.nb_entries);
  /* in WaW, mask can never be 0 */
  assert(mask != 0);
  while (1) {
    if (addr == w->addr) {
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
    assert (w->next != NULL);
    w = w->next;
  }
}

static INLINE int
stm_wbetl_commit(stm_tx_t *tx)
{
  w_entry_t *w;
  stm_version_t t;
  int i;

  PRINT_DEBUG("==> stm_wbetl_commit(%p[%lu-%lu])\n", tx, (unsigned long)tx->start, (unsigned long)tx->end);

  /* A read-only transaction with visible reads must simply drop locks */
  /* FIXME: if killed? */
  if (tx->w_set.has_writes == 0) {
    w = tx->w_set.entries;
    for (i = tx->w_set.nb_entries; i > 0; i--, w++) {
      /* Only drop lock for last covered address in write set */
      if (w->next == NULL)
        LOCK_WRITE_REL(w->lock, LOCK_SET_TIMESTAMP(w->version));
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

  /* Get commit timestamp (may exceed VERSION_MAX by up to MAX_THREADS) */
  t = FETCH_INC_CLOCK + 1;
#ifdef IRREVOCABLE_ENABLED
  if (unlikely(tx->irrevocable))
    goto release_locks;
#endif /* IRREVOCABLE_ENABLED */

  /* Try to validate (only if a concurrent transaction has committed since tx->end) */
  if (unlikely(tx->end != t - 1 && !stm_wbetl_validate(tx))) {
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
  w = tx->w_set.entries;
  for (i = tx->w_set.nb_entries; i > 0; i--, w++) {
    if (w->mask != 0)
      ATOMIC_STORE(w->addr, w->value);
    /* Only drop lock for last covered address in write set */
    if (w->next == NULL) {
      /* In case of visible read, reset lock to its previous timestamp */
      if (w->mask == 0)
        LOCK_WRITE_REL(w->lock, LOCK_SET_TIMESTAMP(w->version));
      else
        LOCK_WRITE_REL(w->lock, LOCK_SET_TIMESTAMP(t));
    }
  }

 end:
  return 1;
}

#endif /* _STM_WBETL_H_ */

