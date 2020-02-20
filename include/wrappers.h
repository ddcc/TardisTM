/*
 * File:
 *   wrappers.h
 * Author(s):
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * Description:
 *   STM wrapper functions for different data types.
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
 *   STM wrapper functions for different data types.  This library
 *   defines transactional loads/store functions for unsigned data types
 *   of various sizes and for basic C data types.
 * @author
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Patrick Marlier <patrick.marlier@unine.ch>
 * @date
 *   2007-2014
 */

#ifndef _WRAPPERS_H_
# define _WRAPPERS_H_

# include <stdint.h>

# include "stm.h"

# ifdef __cplusplus
extern "C" {
# endif

void *stm_load_tag_ptr(const void **addr, const uintptr_t tag) _CALLCONV;
float stm_load_tag_float(const float *addr, const uintptr_t tag) _CALLCONV;
double stm_load_tag_double(const double *addr, const uintptr_t tag) _CALLCONV;

int stm_load_value_ptr(const stm_read_t r, void **value) _CALLCONV;
int stm_load_value_float(const stm_read_t r, float *value) _CALLCONV;
int stm_load_value_double(const stm_read_t r, double *value) _CALLCONV;

int stm_load_update_ptr(const stm_read_t r, void **value) _CALLCONV;
int stm_load_update_float(const stm_read_t r, float *value) _CALLCONV;
int stm_load_update_double(const stm_read_t r, double *value) _CALLCONV;

int stm_store_update_ptr(const stm_write_t w, const void *value) _CALLCONV;
int stm_store_update_float(const stm_write_t w, const float value) _CALLCONV;
int stm_store_update_double(const stm_write_t w, const double value) _CALLCONV;

int stm_store_value_ptr(const stm_write_t w, void **value) _CALLCONV;
int stm_store_value_float(const stm_write_t w, float *value) _CALLCONV;
int stm_store_value_double(const stm_write_t w, double *value) _CALLCONV;

/**
 * Transactional load of an unsigned 8-bit value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
uint8_t stm_load_u8(const uint8_t *addr) _CALLCONV;

/**
 * Transactional load of an unsigned 16-bit value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
uint16_t stm_load_u16(const uint16_t *addr) _CALLCONV;

/**
 * Transactional load of an unsigned 32-bit value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
uint32_t stm_load_u32(const uint32_t *addr) _CALLCONV;

/**
 * Transactional load of an unsigned 64-bit value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
uint64_t stm_load_u64(const uint64_t *addr) _CALLCONV;

/**
 * Transactional load of a char value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
char stm_load_char(const char *addr) _CALLCONV;

/**
 * Transactional load of an unsigned char value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
unsigned char stm_load_uchar(const unsigned char *addr) _CALLCONV;

/**
 * Transactional load of a short value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
short stm_load_short(const short *addr) _CALLCONV;

/**
 * Transactional load of an unsigned short value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
unsigned short stm_load_ushort(const unsigned short *addr) _CALLCONV;

/**
 * Transactional load of an int value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
int stm_load_int(const int *addr) _CALLCONV;

/**
 * Transactional load of an unsigned int value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
unsigned int stm_load_uint(const unsigned int *addr) _CALLCONV;

/**
 * Transactional load of a long value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
long stm_load_long(const long *addr) _CALLCONV;

/**
 * Transactional load of an unsigned long value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
unsigned long stm_load_ulong(const unsigned long *addr) _CALLCONV;


/**
 * Transactional load of a long long value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
long stm_load_llong(const long long *addr) _CALLCONV;

/**
 * Transactional load of an unsigned long long value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
unsigned long stm_load_ullong(const unsigned long long *addr) _CALLCONV;

/**
 * Transactional load of a float value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
float stm_load_float(const float *addr) _CALLCONV;

/**
 * Transactional load of a double value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
double stm_load_double(const double *addr) _CALLCONV;

/**
 * Transactional load of a pointer value.
 *
 * @param addr
 *   Address of the memory location.
 * @return
 *   Value read from the specified address.
 */
void *stm_load_ptr(const void **addr) _CALLCONV;

/**
 * Transactional load of a memory region.  The address of the region
 * does not need to be word aligned and its size may be longer than a
 * word.  The values are copied into the provided buffer, which must be
 * allocated by the caller.
 *
 * @param addr
 *   Address of the memory location.
 * @param buf
 *   Buffer for storing the read bytes.
 * @param size
 *   Number of bytes to read.
 */
void stm_load_bytes(const uint8_t *addr, uint8_t *buf, size_t size) _CALLCONV;

/**
 * Transactional store of an unsigned 8-bit value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_u8(uint8_t *addr, uint8_t value) _CALLCONV;

/**
 * Transactional store of an unsigned 16-bit value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_u16(uint16_t *addr, uint16_t value) _CALLCONV;

/**
 * Transactional store of an unsigned 32-bit value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_u32(uint32_t *addr, uint32_t value) _CALLCONV;

/**
 * Transactional store of an unsigned 64-bit value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_u64(uint64_t *addr, uint64_t value) _CALLCONV;

/**
 * Transactional store of a char value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_char(char *addr, char value) _CALLCONV;

/**
 * Transactional store of an unsigned char value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_uchar(unsigned char *addr, unsigned char value) _CALLCONV;

/**
 * Transactional store of a short value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_short(short *addr, short value) _CALLCONV;

/**
 * Transactional store of an unsigned short value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_ushort(unsigned short *addr, unsigned short value) _CALLCONV;

/**
 * Transactional store of an int value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_int(int *addr, int value) _CALLCONV;

/**
 * Transactional store of an unsigned int value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_uint(unsigned int *addr, unsigned int value) _CALLCONV;

/**
 * Transactional store of a long value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_long(long *addr, long value) _CALLCONV;

/**
 * Transactional store of an unsigned long value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_ulong(unsigned long *addr, unsigned long value) _CALLCONV;

/**
 * Transactional store of a long long value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_llong(long long *addr, long long value) _CALLCONV;

/**
 * Transactional store of an unsigned long long value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_ullong(unsigned long long *addr, unsigned long long value) _CALLCONV;

/**
 * Transactional store of a float value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_float(float *addr, const float value) _CALLCONV;

/**
 * Transactional store of a double value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_double(double *addr, double value) _CALLCONV;

/**
 * Transactional store of a pointer value.
 *
 * @param addr
 *   Address of the memory location.
 * @param value
 *   Value to be written.
 */
void stm_store_ptr(void **addr, const void *value) _CALLCONV;

/**
 * Transactional store of a memory region.  The address of the region
 * does not need to be word aligned and its size may be longer than a
 * word.  The values are copied from the provided buffer.
 *
 * @param addr
 *   Address of the memory location.
 * @param buf
 *   Buffer with the bytes to write.
 * @param size
 *   Number of bytes to write.
 */
void stm_store_bytes(uint8_t *addr, uint8_t *buf, size_t size) _CALLCONV;

/**
 * Transactional write of a byte to a memory region.  The address of the
 * region does not need to be word aligned and its size may be longer
 * than a word.  The provided byte is repeatedly copied to the whole
 * memory region.
 *
 * @param addr
 *   Address of the memory location.
 * @param byte
 *   Byte to write.
 * @param count
 *   Number of bytes to write.
 */
void stm_set_bytes(uint8_t *addr, uint8_t byte, size_t count) _CALLCONV;

# ifdef __cplusplus
}
# endif

#endif /* _WRAPPERS_H_ */
