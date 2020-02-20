/*
 * File:
 *   stm.h
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

/**
 * @file
 *   STM functions.  This library contains the core functions for
 *   programming with STM.
 * @author
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * @date
 *   2007-2014
 */

#ifndef _STM_H_
# define _STM_H_

# include <ffi.h>
# include <setjmp.h>
# include <stdint.h>
# include <stdio.h>
# include <stdlib.h>

/**
 * Version string
 */
# define STM_VERSION                    "1.0.0"
/**
 * Version number (times 100)
 */
# define STM_VERSION_NB                 106

/**
 * Calling convention
 */
# ifdef __i386__
/* The fastcall calling convention improves performance on old ia32
 * architecture that does not implement store forwarding.
 * regparm(3) does not improve significantly the performance. */
#  define _CALLCONV                     __attribute__((fastcall))
# else
#  define _CALLCONV
# endif /* __i386__ */

# ifdef __cplusplus
# include <type_traits>

extern "C" {
# endif

struct stm_tx;
/**
 * Return the current transaction descriptor.
 * The library does not require to pass the current transaction as a
 * parameter to the functions (the current transaction is stored in a
 * thread-local variable).  One can, however, use the library with
 * explicit transaction parameters.  This is useful, for instance, for
 * performance on architectures that do not support TLS or for easier
 * compiler integration.
 */
struct stm_tx *stm_current_tx(void) _CALLCONV;

/* ################################################################### *
 * TYPES
 * ################################################################### */

/**
 * Size of a word (accessible atomically) on the target architecture.
 * The library supports 32-bit and 64-bit architectures.
 */
typedef uintptr_t stm_word_t;

/**
 * Transaction attributes specified by the application.
 */
typedef union stm_tx_attr {
  struct {
  /**
   * Application-specific identifier for the transaction.  Typically,
   * each transactional construct (atomic block) should have a different
   * identifier.  This identifier can be used by the infrastructure for
   * improving performance, for instance by not scheduling together
   * atomic blocks that have conflicted often in the past.
   */
  unsigned int id : 16;
  /**
   * Indicates whether the transaction is read-only.  This information
   * is used as a hint.  If a read-only transaction performs a write, it
   * is aborted and restarted in read-write mode.  In that case, the
   * value of the read-only flag is changed to false.  If no attributes
   * are specified when starting a transaction, it is assumed to be
   * read-write.
   */
  unsigned int read_only : 1;
  /**
   * Indicates whether the transaction should use visible reads.  This
   * information is used when the transaction starts or restarts.  If a
   * transaction automatically switches to visible read mode (e.g.,
   * after having repeatedly aborted with invisible reads), this flag is
   * updated accordingly.  If no attributes are specified when starting
   * a transaction, the default behavior is to use invisible reads.
   */
  unsigned int visible_reads : 1;
  /**
   * Indicates that the transaction should not retry execution using
   * sigsetjmp() after abort.  If no attributes are specified when
   * starting a transaction, the default behavior is to retry.
   */
  unsigned int no_retry : 1;
  /**
   * Indicates that the transaction cannot use the snapshot extension
   * mechanism. (Working only with UNIT_TX)
   */
  unsigned int no_extend : 1;
  /**
   * Indicates that the transaction is irrevocable.
   * 1 is simple irrevocable and 3 is serial irrevocable.
   * (Working only with IRREVOCABLE_ENABLED)
   * TODO Not yet implemented
   */
  /* unsigned int irrevocable : 2; */
  /**
   * Indicates that the transaction should use an ordered read set that supports
   * random insertion.
   */
  unsigned int read_set_ordered : 1;
  /**
   * Indicates that the transaction should not overwrite freed objects to
   * trigger conflicts.
   */
  unsigned int no_overwrite : 1;
  };
  /**
   * All transaction attributes represented as one integer.
   * For convenience, allow (stm_tx_attr_t)0 cast.
   */
  int32_t attrs;
} stm_tx_attr_t;

typedef enum {
  STAT_READ_SET_SIZE,
  STAT_READ_SET_NB_ENTRIES,
  STAT_WRITE_SET_SIZE,
  STAT_WRITE_SET_NB_ENTRIES,
  STAT_WRITE_SET_UNIQUE_SIZE,
  STAT_WRITE_SET_UNIQUE_NB_ENTRIES,
  STAT_OP_LOG_SIZE,
  STAT_OP_LOG_USED,
  STAT_RESTORE_SET_SIZE,
  STAT_RESTORE_SET_NB_ENTRIES,
  STAT_RESTORE_SET_WRITE_SIZE,
  STAT_RESTORE_SET_WRITE_NB_ENTRIES,
  STAT_READ_ONLY,
  STAT_NB_EXTENSIONS,
  STAT_NB_COMMITS,
  STAT_NB_ABORTS,
  STAT_NB_RELOCKS,
  STAT_NB_RETRIES,
  STAT_MAX_RETRIES,
  STAT_AVG_ABORTS,
  STAT_NB_RESTORES_CREATED,
  STAT_NB_RESTORES_EXECUTED,
  STAT_NB_MERGES_MANUAL,
  STAT_NB_MERGES_REPLAY,
  STAT_NB_MERGES_OK,
  STAT_NB_MERGES_RETRY,
  STAT_NB_REVERTED_READS,
  STAT_NB_REVERTED_WRITES,
  STAT_NB_REVERTED_OPS,
  STAT_NB_READS,
  STAT_NB_WRITES,
  STAT_NB_ABORTS_1,
  STAT_NB_ABORTS_2,
  STAT_NB_ABORTS_REASON,
  STAT_NB_ABORTS_LOCKED_READ,
  STAT_NB_ABORTS_LOCKED_WRITE,
  STAT_NB_ABORTS_VALIDATE_READ,
  STAT_NB_ABORTS_VALIDATE_WRITE,
  STAT_NB_ABORTS_VALIDATE_COMMIT,
  STAT_NB_ABORTS_KILLED,
  STAT_NB_ABORTS_INVALID_MEMORY,
  STAT_LOCKED_READS_OK,
  STAT_LOCKED_READS_FAILED,
  STAT_WORK,
  STAT_WORK_MERGE,
} stm_stats_t;

/**
 * Transaction conflict type.
 */
typedef enum {
  STM_RR_CONFLICT = 0x01,
  STM_RW_CONFLICT = 0x02,
  STM_WR_CONFLICT = 0x03,
  STM_WW_CONFLICT = 0x04,
  STM_RD_VALIDATE = 0x05,
  STM_WR_VALIDATE = 0x06,
  STM_CT_VALIDATE = 0x07,
  STM_IRREVOCABLE = 0x08,
  STM_EXPLICIT = 0x09,
  STM_KILLED = 0x0A,
  STM_SIGNAL = 0x0B,
  STM_EXTEND_WS = 0x0C,
  STM_OTHER = 0x0F,
} stm_tx_conflict_t;

/* Sum type of read/write set entry */
typedef unsigned int entry_t;

/* Object representing a transaction read/write set conflict */
typedef struct {
  stm_tx_conflict_t type;               /* Type of conflict */
  entry_t e1;                           /* Read/write set entry 1 */
  entry_t e2;                           /* Read/write set entry 2 */
} stm_conflict_t;

/**
 * Reason for aborting (returned by sigsetjmp() upon transaction
 * restart).
 */
typedef enum {
  /**
   * Indicates that the instrumented code path must be executed.
   */
  STM_PATH_INSTRUMENTED = 0x01,
  /**
   * Indicates that the uninstrumented code path must be executed
   * (serial irrevocable mode).
   */
  STM_PATH_UNINSTRUMENTED = 0x02,
  /**
   * Abort due to explicit call from the programmer.
   */
  STM_ABORT_EXPLICIT = (1UL << 5),
  /**
   * Abort and no retry due to explicit call from the programmer.
   */
  STM_ABORT_NO_RETRY = (1UL << 5) | (1UL << 8),
  /**
   * Implicit abort (high order bits indicate more detailed reason).
   */
  STM_ABORT_IMPLICIT = (1UL << 6),
  /**
   * Abort upon reading a memory location being read by another
   * transaction.
   */
  STM_ABORT_RR_CONFLICT = (1UL << 6) | (STM_RR_CONFLICT << 8),
  /**
   * Abort upon writing a memory location being read by another
   * transaction.
   */
  STM_ABORT_RW_CONFLICT = (1UL << 6) | (STM_RW_CONFLICT << 8),
  /**
   * Abort upon reading a memory location being written by another
   * transaction.
   */
  STM_ABORT_WR_CONFLICT = (1UL << 6) | (STM_WR_CONFLICT << 8),
  /**
   * Abort upon writing a memory location being written by another
   * transaction.
   */
  STM_ABORT_WW_CONFLICT = (1UL << 6) | (STM_WW_CONFLICT << 8),
  /**
   * Abort upon read due to failed validation.
   */
  STM_ABORT_VAL_READ = (1UL << 6) | (STM_RD_VALIDATE << 8),
  /**
   * Abort upon write due to failed validation.
   */
  STM_ABORT_VAL_WRITE = (1UL << 6) | (STM_WR_VALIDATE << 8),
  /**
   * Abort upon commit due to failed validation.
   */
  STM_ABORT_VAL_COMMIT = (1UL << 6) | (STM_CT_VALIDATE << 8),
  /**
   * Abort upon deferring to an irrevocable transaction.
   */
  STM_ABORT_IRREVOCABLE = (1UL << 6) | (STM_IRREVOCABLE << 8),
  /**
   * Abort due to being killed by another transaction.
   */
  STM_ABORT_KILLED = (1UL << 6) | (STM_KILLED << 8),
  /**
   * Abort due to receiving a signal.
   */
  STM_ABORT_SIGNAL = (1UL << 6) | (STM_SIGNAL << 8),
  /**
   * Abort due to reaching the write set size limit.
   */
  STM_ABORT_EXTEND_WS = (1UL << 6) | (STM_EXTEND_WS << 8),
  /**
   * Abort due to other reasons (internal to the protocol).
   */
  STM_ABORT_OTHER = (1UL << 6) | (STM_OTHER << 8)
} stm_tx_abort_t;

/**
 * Policy for contention manager to perform.
 */
typedef enum {
  /**
   * Kill this transaction.
   */
   STM_KILL_SELF = (1UL << 0),
   /**
   * Kill the other transaction.
   */
   STM_KILL_OTHER = (1UL << 1),
   /**
   * Retry this operation.
   */
   STM_RETRY = (1UL << 2),
   /**
   * Skip this conflict.
   */
   STM_SKIP = (1UL << 3),
   /**
   * Flag: Wait on the lock.
   */
   STM_DELAY = (1UL << 4),
} stm_tx_policy_t;

typedef enum stm_merge_policy
#ifdef __cplusplus
  : unsigned int
#endif /* __cplusplus */
{
  /* Regular merge: Indicate that the merge function, if available, should be called to resolve the conflict. */
  STM_MERGE_POLICY_FUNCTION,
  /* Replay merge: Indicate that the STM should undo and replay the conflicting operation. */
  STM_MERGE_POLICY_REPLAY,
} stm_merge_policy_t;

typedef enum stm_merge
#ifdef __cplusplus
  : unsigned int
#endif /* __cplusplus */
{
  /* Merge: Indicate that the merge succeeded. */
  STM_MERGE_OK,
  /* Merge: Indicate that the merge succeeded and must recurse to the parent. */
  STM_MERGE_OK_PARENT,
  /* Merge: Used internally by stm_finish_merge(). */
  STM_MERGE_OK_USER,
  /* Merge: Indicate that the merge is not resolvable and abort. */
  STM_MERGE_ABORT,
  /* Merge: Indicate that the merge should be reattempted. */
  STM_MERGE_RETRY,
  /* Merge: Indicate that this conflict is not resolvable. */
  STM_MERGE_UNSUPPORTED,
} stm_merge_t;

typedef union {
  ffi_sarg sint;
  ffi_arg uint;
  double dbl;
  void *ptr;
} stm_union_t;

typedef enum {
  STM_FEATURE_OPLOG_FULL        = (1UL << 1),
  STM_FEATURE_READ_SET_SOURCE   = (1UL << 2),
  STM_FEATURE_MERGE             = (1UL << 3),
} stm_features_t;

/* Use index-based references to allow resize of underlying array */
/* Use single element struct's for type uniqueness, instead of typedef */
typedef struct stm_op_id { unsigned int idx; } stm_op_id_t;
typedef struct stm_op { unsigned int idx; } stm_op_t;
typedef struct stm_read { unsigned int idx; } stm_read_t;
typedef struct stm_write { unsigned int idx; } stm_write_t;

#ifdef __cplusplus
# define TYPES_COMPATIBLE(a, b)         std::is_same<std::remove_cv<decltype(a)>::type, std::remove_cv<b>::type>::value
#else
# define TYPES_COMPATIBLE(a, b)         __builtin_types_compatible_p(__typeof__(a), b)
#endif /* __cplusplus */

#define STM_BAD_IDX                     ((unsigned int)-2)
#define STM_INVALID_READ                ((stm_read_t){ .idx = STM_BAD_IDX })
#define STM_INVALID_WRITE               ((stm_write_t){ .idx = STM_BAD_IDX })
#define STM_INVALID_OP                  ((stm_op_t){ .idx = STM_BAD_IDX })
#define STM_INVALID_OPID                ((stm_op_id_t){ .idx = STM_BAD_IDX })
#define STM_SAME_READ(a, b)             (TYPES_COMPATIBLE(a, stm_read_t) && TYPES_COMPATIBLE(b, stm_read_t) && (a).idx == (b).idx)
#define STM_SAME_WRITE(a, b)            (TYPES_COMPATIBLE(a, stm_write_t) && TYPES_COMPATIBLE(b, stm_write_t) && (a).idx == (b).idx)
#define STM_SAME_OPID(a, b)             (TYPES_COMPATIBLE(a, stm_op_id_t) && TYPES_COMPATIBLE(b, stm_op_id_t) && (a).idx == (b).idx)
#define STM_SAME_OP(a, b)               (TYPES_COMPATIBLE(a, stm_op_t) && TYPES_COMPATIBLE(b, stm_op_t) && (a).idx == (b).idx)
#define STM_VALID_READ(a)               (TYPES_COMPATIBLE(a, stm_read_t) && !STM_SAME_READ(a, STM_INVALID_READ))
#define STM_VALID_WRITE(a)              (TYPES_COMPATIBLE(a, stm_write_t) && !STM_SAME_WRITE(a, STM_INVALID_WRITE))
#define STM_VALID_OP(a)                 (TYPES_COMPATIBLE(a, stm_op_t) && !STM_SAME_OP(a, STM_INVALID_OP))
#define STM_VALID_OPID(a)               (TYPES_COMPATIBLE(a, stm_op_id_t) && !STM_SAME_OPID(a, STM_INVALID_OPID))

#define ENTRY_INVALID                   (STM_BAD_IDX)
#define ENTRY_VALID(c)                  (c != ENTRY_INVALID)
#define ENTRY_GET_READ(c)               ((stm_read_t){ .idx = (c) })
#define ENTRY_GET_WRITE(c)              ((stm_write_t){ .idx = (c) })

typedef struct stm_merge_context {
  /* Log entry for the current operation being merged */
  stm_op_t current;
  /* Log entry for the previous operation being merged */
  stm_op_t previous;
  /* Address of the conflict */
  const void *addr;
  /* Conflict type  */
  int leaf;
  struct {
    /* An object containing the read/write set entries (valid only when 'leaf' == 1) */
    const stm_conflict_t *entries;
    /* The old and new return values from a merged child operation (valid only when 'leaf' == 0) */
    struct {
      stm_union_t previous_result;
      stm_union_t result;
    };
  } conflict;
  /* Position to insert new read set entries after */
  stm_read_t read;
  /* Return value from the original or replayed operation. Modifications to this value will update the operation log with the new return value, and trigger a recursive merge, with the new value passed as conflict.result.current. */
  stm_union_t rv;
} stm_merge_context_t;

/* Merge function callback type. When a conflict is detected, this function is called, with the conflict passed in 'params' (see 'stm_merge_context_t'). It should return an appropriate merge result (see 'stm_merge_t'). If the result is STM_MERGE_OK, and 'rv' is modified, the merge recurses to the parent of the current operation, and it becomes the new value of 'conflict.result'.

During a merge, the scope of re-execution is set to the operation log entry 'params->current'. With commit-time locking, each read will check for the presence of a previous read (potentially stale) in this scope, and if it exists, will return the corresponding value. Otherwise, it will check for the presence of a previous write in this scope, and if it exists, will return the corresponding value. If neither a previous read nor a previous write exist, then a new read from memory will be recorded in this scope. */
typedef stm_merge_t (*stm_merge_cb_t)(stm_merge_context_t *params);

/* ################################################################### *
 * FUNCTIONS
 * ################################################################### */

const stm_features_t stm_get_features() _CALLCONV;

/* Define a new operation named 's', implemented by a function 'f' with type 'fi'. The return value is the opcode that will identify it in the operation log. This function is not thread safe. The 'policy[0]' variable is used to determine what type of delayed merge is performed upon encountering a conflict, before executing 'delayed'. Likewise, 'policy[1]' is used to determine what type of JIT merge is performed. */
const stm_op_id_t stm_new_opcode(const char *s, const ffi_cif *fi, void (*f)(void), const stm_merge_cb_t delayed, const stm_merge_policy_t policy[2]) _CALLCONV;

/* Log execution begin of the operation with opcode 'op' and arguments '...', and with an optional JIT merge function 'jit'. This merge function takes precedence over that defined in stm_new_op(), if present. */
int stm_begin_op(const stm_op_id_t op, const stm_merge_cb_t jit, ...) _CALLCONV;

/* Log execution end of the operation with opcode 'op' and return value 'ret'. */
int stm_end_op(const stm_op_id_t op, const void *ret) _CALLCONV;

/* Finish the merge. Must be called before jumping back into the original function using goto. */
int stm_finish_merge() _CALLCONV;

/* When merging, check whether address 'addr' was read/written in the scope of the current operation. */
const stm_read_t stm_did_load(const stm_word_t *addr) _CALLCONV;
const stm_write_t stm_did_store(stm_word_t *addr) _CALLCONV;

/* When merging, get the previous value that was read/written from/to address 'addr', and store it in 'value'. */
int stm_load_value(const stm_read_t r, stm_word_t *value) _CALLCONV;
int stm_store_value(const stm_write_t w, stm_word_t *value) _CALLCONV;

/* When merging, update the value of the read 'r' in the scope of the current operation as if the operation were restarted. Returns the updated read value at word granularity. */
int stm_load_update(const stm_read_t r, stm_word_t *value) _CALLCONV;

/* When merging, revert any reads to the read 'r' in the scope of the current operation. */
int stm_undo_load(const stm_read_t r) _CALLCONV;
int stm_undo_load_tx(struct stm_tx *tx, const stm_read_t r) _CALLCONV;

/* When merging, update the value of the write 'w', in the scope of the current operation as if the operation were restarted. */
int stm_store_update(const stm_write_t w, const stm_word_t v) _CALLCONV;
int stm_store2_update(const stm_write_t w, const stm_word_t v, const stm_word_t mask) _CALLCONV;

/* When merging, revert any writes to write 'w' in the scope of the entire transaction. Note that because writes are not versioned at the per-operation level, this will affect all operations in the current transaction. */
int stm_undo_store(const stm_write_t w) _CALLCONV;
int stm_undo_store_tx(struct stm_tx *tx, const stm_write_t w) _CALLCONV;

/* When merging, get/set the tag stored with the opaque read 'r'. */
uintptr_t stm_get_load_tag(const stm_read_t r) _CALLCONV;
int stm_set_load_tag(const stm_read_t r, uintptr_t tag) _CALLCONV;

/* When merging, return the opcode from the opaque read/write/operation log 'r'/'w'/'o'. */
const stm_op_id_t stm_get_op_opcode(const stm_op_t o) _CALLCONV;
const stm_op_id_t stm_get_load_opcode(const stm_read_t r) _CALLCONV;
const stm_op_id_t stm_get_store_opcode(const stm_write_t w) _CALLCONV;

/* When merging, return the read/write address from the opaque read/write 'r'/'w'/'wu'. */
const stm_word_t *stm_get_load_addr(const stm_read_t r) _CALLCONV;
const stm_word_t *stm_get_store_addr(const stm_write_t w) _CALLCONV;

/* When merging, return the corresponding operation log entry for the opaque read/write 'r'/'w', or the current operation from before the merge. */
const stm_op_t stm_get_current_op() _CALLCONV;
const stm_op_t stm_get_load_op(const stm_read_t r) _CALLCONV;
const stm_op_t stm_get_store_op(const stm_write_t w) _CALLCONV;

/* When merging, return the source of the opaque read 'r'. */
const stm_write_t stm_get_load_source(const stm_read_t r);

/* When merging, return the next opaque read of 'r', optionally with the same address and operation. */
const stm_read_t stm_get_load_next(const stm_read_t r, const int op, const int addr);

/* When merging, return the next opaque write of 'w', optionally with the same address. */
const stm_write_t stm_get_store_next(const stm_write_t w, const int addr);

/* When merging, return the last opaque read from the same operation as 'r'. */
const stm_read_t stm_get_load_last(const stm_read_t r);

/* When merging, store a pointer to the arguments of the operation log entry 'o' in 'args'. Returns number of arguments or -1 on error. */
ssize_t stm_get_op_args(const stm_op_t o, const stm_union_t *args[]) _CALLCONV;

/* When merging, store a pointer to the return value of the operation log entry 'o' in 'ret'. Returns the libffi type of the return value. */
unsigned short stm_get_op_ret(const stm_op_t o, stm_union_t *ret) _CALLCONV;

/* When merging, revert any loads/stores/memory operations performed by operation log entry 'o'. */
int stm_clear_op(const stm_op_t o, int read, int write, int mem) _CALLCONV;

/* When merging, revert the subtree rooted at operation log entry 'o'. */
int stm_undo_op(const stm_op_t o) _CALLCONV;

/* When merging, revert any subtrees of the operation log entry 'o' with opcode 'arg'. */
int stm_undo_op_descendants(const stm_op_t o, const stm_op_id_t arg) _CALLCONV;

/* When merging, find the first descendant of the operation log entry 'o' with opcode 'arg'. */
const stm_op_t stm_find_op_descendant(const stm_op_t o, const stm_op_id_t arg) _CALLCONV;

/**
 * Initialize the STM library.  This function must be called once, from
 * the main thread, before any access to the other functions of the
 * library.
 */
void stm_init() _CALLCONV;

/**
 * Clean up the STM library.  This function must be called once, from
 * the main thread, after all transactional threads have completed.
 */
void stm_exit(void) _CALLCONV;

/**
 * Initialize a transactional thread.  This function must be called once
 * from each thread that performs transactional operations, before the
 * thread calls any other functions of the library.
 */
struct stm_tx *stm_init_thread(void) _CALLCONV;

//@{
/**
 * Clean up a transactional thread.  This function must be called once
 * from each thread that performs transactional operations, upon exit.
 */
void stm_exit_thread(void) _CALLCONV;
void stm_exit_thread_tx(struct stm_tx *tx) _CALLCONV;
//@}

//@{
/**
 * Start a transaction.
 *
 * @param attr
 *   Specifies optional attributes associated to the transaction.
 *   Attributes are copied in transaction-local storage.  If null, the
 *   transaction uses default attributes.
 * @return
 *   Environment (stack context) to be used to jump back upon abort.  It
 *   is the responsibility of the application to call sigsetjmp()
 *   immediately after starting the transaction.  If the transaction is
 *   nested, the function returns NULL and one should not call
 *   sigsetjmp() as an abort will restart the top-level transaction
 *   (flat nesting).
 */
sigjmp_buf *stm_start(stm_tx_attr_t attr) _CALLCONV;
sigjmp_buf *stm_start_tx(struct stm_tx *tx, stm_tx_attr_t attr) _CALLCONV;
//@}

//@{
/**
 * Try to commit a transaction.  If successful, the function returns 1.
 * Otherwise, execution continues at the point where sigsetjmp() has
 * been called after starting the outermost transaction (unless the
 * attributes indicate that the transaction should not retry).
 *
 * @return
 *   1 upon success, 0 otherwise.
 */
int stm_commit(void) _CALLCONV;
int stm_commit_tx(struct stm_tx *tx) _CALLCONV;
//@}

//@{
/**
 * Explicitly abort a transaction.  Execution continues at the point
 * where sigsetjmp() has been called after starting the outermost
 * transaction (unless the attributes indicate that the transaction
 * should not retry).
 *
 * @param abort_reason
 *   Reason for aborting the transaction.
 */
void stm_abort(unsigned int abort_reason) _CALLCONV;
void stm_abort_tx(struct stm_tx *tx, unsigned int abort_reason) _CALLCONV;
//@}

/* Abort a transaction, but without restarting it */
void stm_stop(unsigned int abort_reason) _CALLCONV;

/* Force transaction revalidation */
int stm_revalidate();

//@{
/**
 * Transactional load.  Read the specified memory location in the
 * context of the current transaction and return its value.  Upon
 * conflict, the transaction may abort while reading the memory
 * location.  Note that the value returned is consistent with respect to
 * previous reads from the same transaction.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
stm_word_t stm_load(const stm_word_t *addr) _CALLCONV;
stm_word_t stm_load_tx(struct stm_tx *tx, const stm_word_t *addr) _CALLCONV;
//@}

/* Perform a transactional load like stm_load(), but store an additional 'tag' with this read. */
stm_word_t stm_load_tag(const stm_word_t *addr, const uintptr_t tag) _CALLCONV;
stm_word_t stm_load_tag_tx(struct stm_tx *tx, const stm_word_t *addr, const uintptr_t tag) _CALLCONV;

//@{
/**
 * Transactional store.  Write a word-sized value to the specified
 * memory location in the context of the current transaction.  Upon
 * conflict, the transaction may abort while writing to the memory
 * location.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store(stm_word_t *addr, const stm_word_t value) _CALLCONV;
void stm_store_tx(struct stm_tx *tx, stm_word_t *addr, const stm_word_t value) _CALLCONV;
//@}

//@{
/**
 * Transactional store.  Write a value to the specified memory location
 * in the context of the current transaction.  The value may be smaller
 * than a word on the target architecture, in which case a mask is used
 * to indicate the bits of the words that must be updated.  Upon
 * conflict, the transaction may abort while writing to the memory
 * location.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 * @param mask
 *   Mask specifying the bits to be written.
 */
void stm_store2(stm_word_t *addr, stm_word_t value, stm_word_t mask) _CALLCONV;
void stm_store2_tx(struct stm_tx *tx, stm_word_t *addr, stm_word_t value, stm_word_t mask) _CALLCONV;
//@}

//@{
/**
 * Check if the current transaction is still active.
 *
 * @return
 *   True (non-zero) if the transaction is active, false (zero) otherwise.
 */
int stm_active(void) _CALLCONV;
int stm_active_tx(const struct stm_tx *tx) _CALLCONV;
//@}

//@{
/**
 * Check if the current transaction has aborted.
 *
 * @return
 *   True (non-zero) if the transaction has aborted, false (zero) otherwise.
 */
int stm_aborted(void) _CALLCONV;
int stm_aborted_tx(const struct stm_tx *tx) _CALLCONV;
//@}

//@{
/**
 * Check if the current transaction is committing.
 *
 * @return
 *   True (non-zero) if the transaction is committing, false (zero) otherwise.
 */
int stm_committing(void) _CALLCONV;
int stm_committing_tx(const struct stm_tx *tx) _CALLCONV;
//@}

//@{
/**
 * Check if the current transaction is still active and in irrevocable
 * state.
 *
 * @return
 *   True (non-zero) if the transaction is active and irrevocable, false
 *   (zero) otherwise.
 */
int stm_irrevocable(void) _CALLCONV;
int stm_irrevocable_tx(const struct stm_tx *tx) _CALLCONV;
//@}

//@{
/**
 * Check if the current transaction has been killed.
 *
 * @return
 *   True (non-zero) if the transaction has been killed, false (zero) otherwise.
 */
int stm_killed(void) _CALLCONV;
int stm_killed_tx(const struct stm_tx *tx) _CALLCONV;
//@}

//@{
/**
 * Get the environment used by the current thread to jump back upon
 * abort.  This environment should be used when calling sigsetjmp()
 * before starting the transaction and passed as parameter to
 * stm_start().  If the current thread is already executing a
 * transaction, i.e., the new transaction will be nested, the function
 * returns NULL and one should not call sigsetjmp().
 *
 * @return
 *   The environment to use for saving the stack context, or NULL if the
 *   transaction is nested.
 */
sigjmp_buf *stm_get_env(void) _CALLCONV;
sigjmp_buf *stm_get_env_tx(struct stm_tx *tx) _CALLCONV;
//@}

//@{
/**
 * Get attributes associated with the current transactions, if any.
 * These attributes were passed as parameters when starting the
 * transaction.
 *
 * @return Attributes associated with the current transaction, or NULL
 *   if no attributes were specified when starting the transaction.
 */
stm_tx_attr_t stm_get_attributes(void) _CALLCONV;
stm_tx_attr_t stm_get_attributes_tx(const struct stm_tx *tx) _CALLCONV;
//@}

//@{
/**
 * Get various statistics about the current thread/transaction.  See the
 * source code (stm.c) for a list of supported statistics.
 *
 * @param name
 *   Name of the statistics.
 * @param val
 *   Pointer to the variable that should hold the value of the
 *   statistics.
 * @return
 *   1 upon success, 0 otherwise.
 */
int stm_get_stats(const stm_stats_t name, void *val) _CALLCONV;
int stm_get_stats_tx(const struct stm_tx *tx, const stm_stats_t name, void *val) _CALLCONV;
//@}

/**
 * Get various parameters of the STM library.  See the source code
 * (stm.c) for a list of supported parameters.
 *
 * @param name
 *   Name of the parameter.
 * @param val
 *   Pointer to the variable that should hold the value of the
 *   parameter.
 * @return
 *   1 upon success, 0 otherwise.
 */
int stm_get_parameter(const char *name, void *val) _CALLCONV;

/**
 * Set various parameters of the STM library.  See the source code
 * (stm.c) for a list of supported parameters.
 *
 * @param name
 *   Name of the parameter.
 * @param val
 *   Pointer to a variable that holds the new value of the parameter.
 * @return
 *   1 upon success, 0 otherwise.
 */
int stm_set_parameter(const char *name, void *val) _CALLCONV;

/**
 * Create a key to associate application-specific data to the current
 * thread/transaction.  This mechanism can be combined with callbacks to
 * write modules.
 *
 * @return
 *   The new key.
 */
int stm_create_specific(void) _CALLCONV;

//@{
/**
 * Get application-specific data associated to the current
 * thread/transaction and a given key.
 *
 * @param key
 *   Key designating the data to read.
 * @return
 *   Data stored under the given key.
 */
void *stm_get_specific(const int key) _CALLCONV;
void *stm_get_specific_tx(const struct stm_tx *tx, const int key) _CALLCONV;
//@}

//@{
/**
 * Set application-specific data associated to the current
 * thread/transaction and a given key.
 *
 * @param key
 *   Key designating the data to read.
 * @param data
 *   Data to store under the given key.
 */
void stm_set_specific(int key, const void *data) _CALLCONV;
void stm_set_specific_tx(struct stm_tx *tx, const int key, const void *data) _CALLCONV;
//@}

/**
 * Register application-specific callbacks that are triggered each time
 * particular events occur.
 *
 * @param on_thread_init
 *   Function called upon initialization of a transactional thread.
 * @param on_thread_exit
 *   Function called upon cleanup of a transactional thread.
 * @param on_start
 *   Function called upon start of a transaction.
 * @param on_precommit
 *   Function called before transaction try to commit.
 * @param on_commit
 *   Function called upon successful transaction commit.
 * @param on_abort
 *   Function called upon transaction abort.
 * @param arg
 *   Parameter to be passed to the callback functions.
 * @return
 *   1 if the callbacks have been successfully registered, 0 otherwise.
 */
int stm_register(void (* const on_thread_init)(struct stm_tx *tx, const void *arg),
                 void (* const on_thread_exit)(const struct stm_tx *tx, const void *arg),
                 void (* const on_start)(const struct stm_tx *tx, const void *arg),
                 void (* const on_precommit)(const struct stm_tx *tx, const void *arg),
                 void (* const on_commit)(const struct stm_tx *tx, const void *arg),
                 void (* const on_abort)(const struct stm_tx *tx, const stm_tx_abort_t reason, const void *arg),
                 void *arg) _CALLCONV;

/**
 * Transaction-safe load.  Read the specified memory location outside of
 * the context of any transaction and return its value.  The operation
 * behaves as if executed in the context of a dedicated transaction
 * (i.e., it executes atomically and in isolation) that never aborts,
 * but may get delayed.
 *
 * @param addr Address of the memory location.

 * @param timestamp If non-null, the referenced variable is updated to
 *   hold the timestamp of the memory location being read.
 * @return
 *   Value read from the specified address.
 */
stm_word_t stm_unit_load(stm_word_t *addr, stm_word_t *timestamp) _CALLCONV;

/**
 * Transaction-safe store.  Write a word-sized value to the specified
 * memory location outside of the context of any transaction.  The
 * operation behaves as if executed in the context of a dedicated
 * transaction (i.e., it executes atomically and in isolation) that
 * never aborts, but may get delayed.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 * @param timestamp If non-null and the timestamp in the referenced
 *   variable is smaller than that of the memory location being written,
 *   no data is actually written and the variable is updated to hold the
 *   more recent timestamp. If non-null and the timestamp in the
 *   referenced variable is not smaller than that of the memory location
 *   being written, the memory location is written and the variable is
 *   updated to hold the new timestamp.
 * @return
 *   1 if value has been written, 0 otherwise.
 */
int stm_unit_store(stm_word_t *addr, stm_word_t value, stm_word_t *timestamp) _CALLCONV;

/**
 * Transaction-safe store.  Write a value to the specified memory
 * location outside of the context of any transaction.  The value may be
 * smaller than a word on the target architecture, in which case a mask
 * is used to indicate the bits of the words that must be updated.  The
 * operation behaves as if executed in the context of a dedicated
 * transaction (i.e., it executes atomically and in isolation) that
 * never aborts, but may get delayed.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 * @param mask
 *   Mask specifying the bits to be written.
 * @param timestamp If non-null and the timestamp in the referenced
 *   variable is smaller than that of the memory location being written,
 *   no data is actually written and the variable is updated to hold the
 *   more recent timestamp. If non-null and the timestamp in the
 *   referenced variable is not smaller than that of the memory location
 *   being written, the memory location is written and the variable is
 *   updated to hold the new timestamp.
 * @return
 *   1 if value has been written, 0 otherwise.
 */
int stm_unit_store2(stm_word_t *addr, stm_word_t value, stm_word_t mask, stm_word_t *timestamp) _CALLCONV;

//@{
/**
 * Enable or disable snapshot extensions for the current transaction,
 * and optionally set an upper bound for the snapshot.  This function is
 * useful for implementing efficient algorithms with unit loads and
 * stores while preserving compatibility with with regular transactions.
 *
 * @param enable
 *   True (non-zero) to enable snapshot extensions, false (zero) to
 *   disable them.
 * @param timestamp
 *   If non-null and the timestamp in the referenced variable is smaller
 *   than the current upper bound of the snapshot, update the upper
 *   bound to the value of the referenced variable.
 */
void stm_set_extension(int enable, stm_word_t *timestamp) _CALLCONV;
void stm_set_extension_tx(struct stm_tx *tx, int enable, stm_word_t *timestamp) _CALLCONV;
//@}

/**
 * Read the current value of the global clock (used for timestamps).
 * This function is useful when programming with unit loads and stores.
 *
 * @return
 *   Value of the global clock.
 */
const stm_word_t stm_get_clock(void) _CALLCONV;

//@{
/**
 * Enter irrevocable mode for the current transaction.  If successful,
 * the function returns 1.  Otherwise, it aborts and execution continues
 * at the point where sigsetjmp() has been called after starting the
 * outermost transaction (unless the attributes indicate that the
 * transaction should not retry).
 *
 * @param serial
 *   True (non-zero) for serial-irrevocable mode (no transaction can
 *   execute concurrently), false for parallel-irrevocable mode.
 * @return
 *   1 upon success, 0 otherwise.
 */
int stm_set_irrevocable(int serial) _CALLCONV;
int stm_set_irrevocable_tx(struct stm_tx *tx, int serial) _CALLCONV;
//@}

#ifdef __cplusplus
}
#endif

#endif /* _STM_H_ */
