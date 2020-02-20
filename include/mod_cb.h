/*
 * File:
 *   mod_cb.h
 * Author(s):
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * Description:
 *   Module for user callbacks.
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

/**
 * @file
 *   Module for user callbacks.
 * @author
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * @date
 *   2007-2014
 */

#ifndef _MOD_CB_H_
# define _MOD_CB_H_

# include "stm.h"

# ifdef __cplusplus
extern "C" {
# endif

/**
 * Register an application-specific callback triggered when the current
 * transaction commits.  The callback is automatically unregistered once
 * the transaction commits or aborts.  If the transaction aborts, the
 * callback is never triggered.
 *
 * @param on_commit
 *   Function called upon successful transaction commit.
 * @param arg
 *   Parameter to be passed to the callback function.
 * @return
 *   1 if the callbacks have been successfully registered, 0 otherwise.
 */
int stm_on_commit(const void (*on_commit)(const struct stm_tx *tx, const void *arg), const void *arg, const stm_op_t o);

/**
 * Register an application-specific callback triggered when the current
 * transaction aborts.  The callback is automatically unregistered once
 * the transaction commits or aborts.  If the transaction commits, the
 * callback is never triggered.
 *
 * @param on_abort
 *   Function called upon transaction abort.
 * @param arg
 *   Parameter to be passed to the callback function.
 * @return
 *   1 if the callbacks have been successfully registered, 0 otherwise.
 */
int stm_on_abort(const void (*on_abort)(const struct stm_tx *tx, const stm_tx_abort_t reason, const void *arg), const void *arg, const stm_op_t o);

# ifdef __cplusplus
}
# endif

#endif /* _MOD_CB_H_ */
