/*
 * File:
 *   mod_stats.c
 * Author(s):
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * Description:
 *   Module for gathering global statistics about transactions.
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
#include <limits.h>
#include <stdio.h>
#include <string.h>

#include "mod_stats.h"

#include "atomic.h"
#include "stm.h"
#include "utils.h"

#include "stm_internal.h"

#define MAX_HIST                        8

/* ################################################################### *
 * TYPES
 * ################################################################### */

typedef struct mod_stats_data {         /* Transaction statistics */
  atomic_ulong max_rs_entries;          /* Maximum number of read set entries */
  atomic_ulong rs_entries;              /* Total number of read set entries */
  atomic_ulong rs_entries_aborted;      /* Total number of read set entries in aborted transactions */
  atomic_ulong max_ws_entries;          /* Maximum number of write set entries */
  atomic_ulong ws_entries;              /* Total number of write set entries */
  atomic_ulong ws_entries_aborted;      /* Total number of write set entries in aborted transactions */
  atomic_ulong max_ws_unique_entries;   /* Maximum number of write set unique entries */
  atomic_ulong ws_unique_entries;       /* Total number of write set unique entries */
  atomic_ulong ws_unique_entries_aborted; /* Total number of write set unique entries in aborted transactions */
  atomic_ulong ws_unique_entries_nonempty; /* Total number of non-empty write set unique entries in committed transactions */
#if OPERATION_LOGGING == OPLOG_FULL
  atomic_ulong max_ol_used;             /* Maximum operation log bytes used  */
  atomic_ulong ol_used;                 /* Total operation log bytes used */
  atomic_ulong ol_used_aborted;         /* Total operation log bytes used in aborted transactions */
#endif /* OPERATION_LOGGING */
#ifdef TM_STATISTICS
  atomic_ulong extensions;              /* Total number of extensions (cumulative) */
  atomic_ulong commits;                 /* Total number of commits (cumulative) */
  atomic_ulong aborts;                  /* Total number of aborts (cumulative) */
  atomic_ulong relocks;                 /* Total number of relocks (cumulative) */
  atomic_ulong max_retries;             /* Maximum number of consecutive aborts (retries) */
# if CM == CM_MERGE
  atomic_ulong merges_manual;           /* Total number of manual merges started (cumulative) */
  atomic_ulong merges_replay;           /* Total number of replay merges started (cumulative) */
  atomic_ulong merges_ok;               /* Total number of merges successfully finished (cumulative) */
  atomic_ulong merges_retry;            /* Total number of merges resulting in a retry (cumulative) */
  atomic_ulong reverted_reads;          /* Total number of reverted reads (cumulative) */
  atomic_ulong reverted_writes;         /* Total number of reverted writes (cumulative) */
  atomic_ulong reverted_ops;            /* Total number of reverted operations (cumulative) */
  atomic_ulong commits_m[MAX_HIST];     /* Histogram of total successful merges across committed transactions (cumulative) */
  atomic_ulong aborts_m[MAX_HIST];      /* Histogram of total successful merges across aborted transactions (cumulative) */
# endif /* CM == CM_MERGE */
#endif /* TM_STATISTICS */
#ifdef TM_STATISTICS2
  atomic_llong work_first_order;        /* Total sum of cycle count before first merge from committed transactions (work saved), minus total sum of cycle count after first merge from aborted transactions (additional work expended) */
  atomic_ullong work_committed;         /* Total cycle count of committed transactions (cumulative) */
  atomic_ullong work_aborted;           /* Total cycle count of aborted transactions (cumulative) */
  atomic_ullong work_merge_before;      /* Total cycle count before first merge (cumulative) */
  atomic_ullong work_merge_after;       /* Total cycle count after first merge (cumulative) */
  atomic_ulong reads;                   /* Total number of reads (cumulative) */
  atomic_ulong writes;                  /* Total number of writes (cumulative) */
  atomic_ulong aborts_r[16];            /* Total number of aborts by reason (cumulative) */
#endif /* TM_STATISTICS2 */
} mod_stats_data_t;

static int mod_stats_initialized = 0;
static mod_stats_data_t mod_stats_global = { 0 };

/* ################################################################### *
 * FUNCTIONS
 * ################################################################### */

/*
 * Return aggregate statistics about transactions.
 */
int stm_get_global_stats(const char *name, void *val)
{
  if (!mod_stats_initialized) {
    fprintf(stderr, "Module mod_stats not initialized\n");
    exit(1);
  }

  if (strcmp("global_max_rs_entries", name) == 0) {
    *(unsigned long *)val = mod_stats_global.max_rs_entries;
    return 1;
  }
  if (strcmp("global_nb_rs_entries", name) == 0) {
    *(unsigned long *)val = mod_stats_global.rs_entries;
    return 1;
  }
  if (strcmp("global_nb_rs_entries_aborted", name) == 0) {
    *(unsigned long *)val = mod_stats_global.rs_entries_aborted;
    return 1;
  }
  if (strcmp("global_max_ws_entries", name) == 0) {
    *(unsigned long *)val = mod_stats_global.max_ws_entries;
    return 1;
  }
  if (strcmp("global_nb_ws_entries", name) == 0) {
    *(unsigned long *)val = mod_stats_global.ws_entries;
    return 1;
  }
  if (strcmp("global_nb_ws_entries_aborted", name) == 0) {
    *(unsigned long *)val = mod_stats_global.ws_entries_aborted;
    return 1;
  }
  if (strcmp("global_max_ws_unique_entries", name) == 0) {
    *(unsigned long *)val = mod_stats_global.max_ws_unique_entries;
    return 1;
  }
  if (strcmp("global_nb_ws_unique_entries", name) == 0) {
    *(unsigned long *)val = mod_stats_global.ws_unique_entries;
    return 1;
  }
  if (strcmp("global_nb_ws_unique_entries_aborted", name) == 0) {
    *(unsigned long *)val = mod_stats_global.ws_unique_entries_aborted;
    return 1;
  }
  if (strcmp("global_nb_ws_unique_entries_nonempty", name) == 0) {
    *(unsigned long *)val = mod_stats_global.ws_unique_entries_nonempty;
    return 1;
  }

#if OPERATION_LOGGING == OPLOG_FULL
  if (strcmp("global_max_ol_used", name) == 0) {
    *(unsigned long *)val = mod_stats_global.max_ol_used;
    return 1;
  }
  if (strcmp("global_ol_used", name) == 0) {
    *(unsigned long *)val = mod_stats_global.ol_used;
    return 1;
  }
  if (strcmp("global_ol_used_aborted", name) == 0) {
    *(unsigned long *)val = mod_stats_global.ol_used_aborted;
    return 1;
  }
#endif /* OPERATION_LOGGING */

#ifdef TM_STATISTICS
  if (strcmp("global_nb_extensions", name) == 0) {
    *(unsigned long *)val = mod_stats_global.extensions;
    return 1;
  }
  if (strcmp("global_nb_commits", name) == 0) {
    *(unsigned long *)val = mod_stats_global.commits;
    return 1;
  }
  if (strcmp("global_nb_aborts", name) == 0) {
    *(unsigned long *)val = mod_stats_global.aborts;
    return 1;
  }
  if (strcmp("global_nb_relocks", name) == 0) {
    *(unsigned long *)val = mod_stats_global.relocks;
    return 1;
  }
  if (strcmp("global_max_retries", name) == 0) {
    *(unsigned long *)val = mod_stats_global.max_retries;
    return 1;
  }

# if CM == CM_MERGE
  if (strcmp("global_nb_merges_manual", name) == 0) {
    *(unsigned long *)val = mod_stats_global.merges_manual;
    return 1;
  }
  if (strcmp("global_nb_merges_replay", name) == 0) {
    *(unsigned long *)val = mod_stats_global.merges_replay;
    return 1;
  }
  if (strcmp("global_nb_merges_ok", name) == 0) {
    *(unsigned long *)val = mod_stats_global.merges_ok;
    return 1;
  }
  if (strcmp("global_nb_merges_retry", name) == 0) {
    *(unsigned long *)val = mod_stats_global.merges_retry;
    return 1;
  }
  if (strcmp("global_nb_reverted_reads", name) == 0) {
    *(unsigned long *)val = mod_stats_global.reverted_reads;
    return 1;
  }
  if (strcmp("global_nb_reverted_writes", name) == 0) {
    *(unsigned long *)val = mod_stats_global.reverted_writes;
    return 1;
  }
  if (strcmp("global_nb_reverted_ops", name) == 0) {
    *(unsigned long *)val = mod_stats_global.reverted_ops;
    return 1;
  }
  if (strcmp("max_history", name) == 0) {
    *(unsigned long *)val = MAX_HIST;
    return 1;
  }
  if (strcmp("global_nb_commits_merges", name) == 0) {
    memcpy(val, mod_stats_global.commits_m, sizeof(mod_stats_global.commits_m));
    return 1;
  }
  if (strcmp("global_nb_aborts_merges", name) == 0) {
    memcpy(val, mod_stats_global.aborts_m, sizeof(mod_stats_global.aborts_m));
    return 1;
  }
# endif /* CM == CM_MERGE */
#endif /* TM_STATISTICS */

#ifdef TM_STATISTICS2
  if (strcmp("global_nb_reads", name) == 0) {
    *(unsigned long *)val = mod_stats_global.reads;
    return 1;
  }
  if (strcmp("global_nb_writes", name) == 0) {
    *(unsigned long *)val = mod_stats_global.writes;
    return 1;
  }
  if (strcmp("global_nb_aborts_reason", name) == 0) {
    memcpy(val, mod_stats_global.aborts_r, sizeof(mod_stats_global.aborts_r));
    return 1;
  }
  if (strcmp("global_work_aborted", name) == 0) {
    *(unsigned long long *)val = mod_stats_global.work_aborted;
    return 1;
  }
  if (strcmp("global_work_committed", name) == 0) {
    *(unsigned long long *)val = mod_stats_global.work_committed;
    return 1;
  }
  if (strcmp("global_work_merge_before", name) == 0) {
    *(unsigned long long *)val = mod_stats_global.work_merge_before;
    return 1;
  }
  if (strcmp("global_work_merge_after", name) == 0) {
    *(unsigned long long *)val = mod_stats_global.work_merge_after;
    return 1;
  }
  if (strcmp("global_work_first_order", name) == 0) {
    *(long long *)val = mod_stats_global.work_first_order;
    return 1;
  }
#endif /* TM_STATISTICS2 */

  return 0;
}

/*
 * Called upon thread deletion.
 */
static void mod_stats_on_thread_exit(const struct stm_tx *tx, const void *arg)
{
#ifdef TM_STATISTICS2
  unsigned int ival[16];
#endif /* TM_STATISTICS2 */
  unsigned long lval1 = 0, lval2 = 0;

#ifdef TM_STATISTICS
  if (stm_get_stats_tx(tx, STAT_NB_EXTENSIONS, &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.extensions, lval1);
  if (stm_get_stats_tx(tx, STAT_NB_COMMITS, &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.commits, lval1);
  if (stm_get_stats_tx(tx, STAT_NB_ABORTS, &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.aborts, lval1);
  if (stm_get_stats_tx(tx, STAT_NB_RELOCKS, &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.relocks, lval1);
  if (stm_get_stats_tx(tx, STAT_MAX_RETRIES, &lval1)) {
retry_max:
    lval2 = ATOMIC_LOAD(&mod_stats_global.max_retries);
    if (lval1 > lval2) {
      if (ATOMIC_CAS_FULL(&mod_stats_global.max_retries, lval2, lval1) == 0)
        goto retry_max;
    }
  }
#endif /* TM_STATISTICS */

#ifdef TM_STATISTICS2
  if (stm_get_stats_tx(tx, STAT_NB_READS, &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.reads, lval1);
  if (stm_get_stats_tx(tx, STAT_NB_WRITES, &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.writes, lval1);
  if (stm_get_stats_tx(tx, STAT_NB_ABORTS_REASON, ival)) {
    for (unsigned i = 0; i < sizeof(mod_stats_global.aborts_r) / sizeof(mod_stats_global.aborts_r[0]); ++i) {
      if (i != STM_COMMIT_MERGED && i != STM_ABORT_MERGED)
        ATOMIC_FETCH_ADD_FULL(&mod_stats_global.aborts_r[i], ival[i]);
      else
        assert(ival[i] == 0);
    }
  }
#endif /* TM_STATISTICS2 */
}

#ifdef TM_STATISTICS
static void mod_stats_common(const struct stm_tx *tx, const void *arg, int commit) {
  unsigned long lval1 = 0, lval2 = 0;
# if CM == CM_MERGE
  unsigned long merges_manual = 0, merges_replay = 0, merges_rollback = 0;
# endif /* CM == CM_MERGE */

#ifdef TM_STATISTICS2
  unsigned long long ullval1;
  unsigned long long ullval2 = get_time();
  if (stm_get_stats_tx(tx, STAT_WORK, &ullval1)) {
    ATOMIC_FETCH_ADD_FULL(commit ? &mod_stats_global.work_committed : &mod_stats_global.work_aborted, ullval2 - ullval1);
  }
  unsigned long long ullval3;
  if (stm_get_stats_tx(tx, STAT_WORK_MERGE, &ullval3) && ullval3) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.work_merge_before, ullval3 - ullval1);
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.work_merge_after, ullval2 - ullval3);

    if (commit)
      ATOMIC_FETCH_ADD_FULL(&mod_stats_global.work_first_order, ullval3 - ullval1);
    else
      ATOMIC_FETCH_SUB_FULL(&mod_stats_global.work_first_order, ullval2 - ullval3);
  }
#endif /* TM_STATISTICS2 */

  if (stm_get_stats_tx(tx, STAT_READ_SET_NB_ENTRIES, &lval1)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.rs_entries, lval1);
    if (!commit)
      ATOMIC_FETCH_ADD_FULL(&mod_stats_global.rs_entries_aborted, lval1);
rs_max:
    lval2 = ATOMIC_LOAD(&mod_stats_global.max_rs_entries);
    if (lval1 > lval2) {
      if (ATOMIC_CAS_FULL(&mod_stats_global.max_rs_entries, lval2, lval1) == 0)
        goto rs_max;
    }
  }

  if (stm_get_stats_tx(tx, STAT_WRITE_SET_NB_ENTRIES, &lval1)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.ws_entries, lval1);
    if (!commit)
      ATOMIC_FETCH_ADD_FULL(&mod_stats_global.ws_entries_aborted, lval1);
ws_max:
    lval2 = ATOMIC_LOAD(&mod_stats_global.max_ws_entries);
    if (lval1 > lval2) {
      if (ATOMIC_CAS_FULL(&mod_stats_global.max_ws_entries, lval2, lval1) == 0)
        goto ws_max;
    }
  }

  if (stm_get_stats_tx(tx, STAT_WRITE_SET_UNIQUE_NB_ENTRIES, &lval1)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.ws_unique_entries, lval1);
    if (!commit)
      ATOMIC_FETCH_ADD_FULL(&mod_stats_global.ws_unique_entries_aborted, lval1);
    else {
# if WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE
      for (w_entry_unique_t *wu = tx->w_set_unique.entries + tx->w_set_unique.nb_entries - 1; likely(wu >= tx->w_set_unique.entries + WRITE_RESERVED_IDX + 1); --wu)
# else
      for (w_entry_unique_t *wu = tx->w_set_unique.entries + tx->w_set_unique.nb_entries - 1; likely(wu >= tx->w_set_unique.entries); --wu)
# endif /* WRITE_SET_UNIQUE == RW_HASH_TABLE || WRITE_SET_UNIQUE == RW_ADAPTIVE */
      {
        if (WRITE_VALID_FAST(tx, wu->latest))
          ATOMIC_FETCH_INC_FULL(&mod_stats_global.ws_unique_entries_nonempty);
      }
    }
ws_unique_max:
    lval2 = ATOMIC_LOAD(&mod_stats_global.max_ws_unique_entries);
    if (lval1 > lval2) {
      if (ATOMIC_CAS_FULL(&mod_stats_global.max_ws_unique_entries, lval2, lval1) == 0)
        goto ws_unique_max;
    }
  }

# if OPERATION_LOGGING == OPLOG_FULL
  if (stm_get_stats_tx(tx, STAT_OP_LOG_USED, &lval1)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.ol_used, lval1);
    if (!commit)
      ATOMIC_FETCH_ADD_FULL(&mod_stats_global.ol_used_aborted, lval1);
ol_max:
    lval2 = ATOMIC_LOAD(&mod_stats_global.max_ol_used);
    if (lval1 > lval2) {
      if (ATOMIC_CAS_FULL(&mod_stats_global.max_ol_used, lval2, lval1) == 0)
        goto ol_max;
    }
  }
# endif /* OPERATION_LOGGING */

# if CM == CM_MERGE
  if (stm_get_stats_tx(tx, STAT_NB_MERGES_OK, &lval1)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.merges_ok, lval1);

    unsigned int off = lval1 >= MAX_HIST ? MAX_HIST - 1 : lval1;
    ATOMIC_FETCH_INC_FULL(commit ? &mod_stats_global.commits_m[off] : &mod_stats_global.aborts_m[off]);
  }

  if (stm_get_stats_tx(tx, STAT_NB_MERGES_RETRY, &lval1)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.merges_retry, lval1);
  }

  if (stm_get_stats_tx(tx, STAT_NB_REVERTED_READS, &lval1)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.reverted_reads, lval1);
  }

  if (stm_get_stats_tx(tx, STAT_NB_REVERTED_WRITES, &lval1)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.reverted_writes, lval1);
  }

  if (stm_get_stats_tx(tx, STAT_NB_REVERTED_OPS, &lval1)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.reverted_ops, lval1);
  }

  if (stm_get_stats_tx(tx, STAT_NB_MERGES_MANUAL, &merges_manual)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.merges_manual, merges_manual);
  }

  if (stm_get_stats_tx(tx, STAT_NB_MERGES_REPLAY, &merges_replay)) {
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.merges_replay, merges_replay);
  }

  if (merges_manual || merges_replay || merges_rollback) {
    // Transactions with conflicts handled by merge constraint manager that commit or abort
    ATOMIC_FETCH_INC_FULL(&mod_stats_global.aborts_r[commit ? STM_COMMIT_MERGED : STM_ABORT_MERGED]);
  }
# endif /* CM == CM_MERGE */
}

/*
 * Called upon transaction commit.
 */
static void mod_stats_on_commit(const struct stm_tx *tx, const void *arg)
{
  mod_stats_common(tx, arg, 1);
}

/*
 * Called upon transaction abort.
 */
static void mod_stats_on_abort(const struct stm_tx *tx, const stm_tx_abort_t reason, const void *arg)
{
  mod_stats_common(tx, arg, 0);
}
#endif /* TM_STATISTICS */

/*
 * Initialize module.
 */
void mod_stats_init(void)
{
  if (mod_stats_initialized)
    return;

#ifdef TM_STATISTICS
  if (!stm_register(NULL, mod_stats_on_thread_exit, NULL, NULL, mod_stats_on_commit, mod_stats_on_abort, NULL))
#else
  if (!stm_register(NULL, mod_stats_on_thread_exit, NULL, NULL, NULL, NULL, NULL))
#endif /* TM_STATISTICS */
  {
    fprintf(stderr, "Cannot register callbacks\n");
    exit(1);
  }

  mod_stats_initialized = 1;
}
