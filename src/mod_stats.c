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

/* ################################################################### *
 * TYPES
 * ################################################################### */

typedef struct mod_stats_data {         /* Transaction statistics */
  unsigned long max_rs_entries;         /* Maximum number of read set entries */
  unsigned long max_ws_entries;         /* Maximum number of write set entries */
#ifdef TM_STATISTICS
  unsigned long commits;                /* Total number of commits (cumulative) */
  unsigned long aborts;                 /* Total number of aborts (cumulative) */
  unsigned long retries;                /* Total number of consecutive aborts (retries) */
  unsigned long max_retries;            /* Maximum number of consecutive aborts (retries) */
#endif /* TM_STATISTICS */
#ifdef TM_STATISTICS2
  unsigned long reads;                  /* Total number of reads (cumulative) */
  unsigned long writes;                 /* Total number of writes (cumulative) */
  unsigned long aborts_r[16];           /* Total number of aborts by reason (cumulative) */
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
  if (strcmp("global_max_ws_entries", name) == 0) {
    *(unsigned long *)val = mod_stats_global.max_ws_entries;
    return 1;
  }

#ifdef TM_STATISTICS
  if (strcmp("global_nb_commits", name) == 0) {
    *(unsigned long *)val = mod_stats_global.commits;
    return 1;
  }
  if (strcmp("global_nb_aborts", name) == 0) {
    *(unsigned long *)val = mod_stats_global.aborts;
    return 1;
  }
  if (strcmp("global_nb_retries", name) == 0) {
    *(unsigned long *)val = mod_stats_global.retries;
    return 1;
  }
  if (strcmp("global_max_retries", name) == 0) {
    *(unsigned long *)val = mod_stats_global.max_retries;
    return 1;
  }
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

  if (stm_get_stats_tx(tx, "read_set_nb_entries", &lval1)) {
rs_max:
    lval2 = ATOMIC_LOAD(&mod_stats_global.max_rs_entries);
    if (lval1 > lval2) {
      if (ATOMIC_CAS_FULL(&mod_stats_global.max_rs_entries, lval2, lval1) == 0)
        goto rs_max;
    }
  }
  if (stm_get_stats_tx(tx, "write_set_nb_entries", &lval1)) {
ws_max:
    lval2 = ATOMIC_LOAD(&mod_stats_global.max_ws_entries);
    if (lval1 > lval2) {
      if (ATOMIC_CAS_FULL(&mod_stats_global.max_ws_entries, lval2, lval1) == 0)
        goto ws_max;
    }
  }

#ifdef TM_STATISTICS
  if (stm_get_stats_tx(tx, "nb_commits", &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.commits, lval1);
  if (stm_get_stats_tx(tx, "nb_aborts", &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.aborts, lval1);
  if (stm_get_stats_tx(tx, "nb_retries", &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.retries, lval1);
  if (stm_get_stats_tx(tx, "max_retries", &lval1)) {
retry_max:
    lval2 = ATOMIC_LOAD(&mod_stats_global.max_retries);
    if (lval1 > lval2) {
      if (ATOMIC_CAS_FULL(&mod_stats_global.max_retries, lval2, lval1) == 0)
        goto retry_max;
    }
  }
#endif /* TM_STATISTICS */

#ifdef TM_STATISTICS2
  if (stm_get_stats_tx(tx, "nb_reads", &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.reads, lval1);
  if (stm_get_stats_tx(tx, "nb_writes", &lval1))
    ATOMIC_FETCH_ADD_FULL(&mod_stats_global.writes, lval1);
  if (stm_get_stats_tx(tx, "nb_aborts_reason", ival)) {
    for (unsigned i = 0; i < sizeof(mod_stats_global.aborts_r) / sizeof(mod_stats_global.aborts_r[0]); ++i) {
      if (i != STM_COMMIT_MERGED && i != STM_ABORT_MERGED)
        ATOMIC_FETCH_ADD_FULL(&mod_stats_global.aborts_r[i], ival[i]);
      else
        assert(ival[i] == 0);
    }
  }
#endif /* TM_STATISTICS2 */
}

/*
 * Initialize module.
 */
void mod_stats_init(void)
{
  if (mod_stats_initialized)
    return;

  if (!stm_register(NULL, mod_stats_on_thread_exit, NULL, NULL, NULL, NULL, NULL))
  {
    fprintf(stderr, "Cannot register callbacks\n");
    exit(1);
  }

  mod_stats_initialized = 1;
}
