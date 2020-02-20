/*
 * File:
 *   wrappers.c
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

#include <assert.h>

#include "utils.h"
#include "stm_internal.h"
#include "wrappers.h"

#define ALLOW_MISALIGNED_ACCESSES

#define TM_LOAD(addr)                stm_load(addr)
#define TM_LOAD_TAG(addr, tag)       stm_load_tag(addr, tag)
#define TM_LOAD_UPDATE               stm_load_update
#define TM_LOAD_VALUE                stm_load_value
#define TM_STORE(addr, val)          stm_store(addr, val)
#define TM_STORE_UPDATE(w, val)      stm_store_update(w, val)
#define TM_STORE2(addr, val, mask)   stm_store2(addr, val, mask)
#define TM_STORE2_UPDATE(w, val, mask) stm_store2_update(w, val, mask)
#define TM_STORE_VALUE                stm_store_value

typedef union convert_64 {
  uint64_t u64;
  uint32_t u32[2];
  uint16_t u16[4];
  uint8_t u8[8];
  int64_t s64;
  double d;
} convert_64_t;

typedef union convert_32 {
  uint32_t u32;
  uint16_t u16[2];
  uint8_t u8[4];
  int32_t s32;
  float f;
} convert_32_t;

typedef union convert_16 {
  uint16_t u16;
  int16_t s16;
} convert_16_t;

typedef union convert_8 {
  uint8_t u8;
  int8_t s8;
} convert_8_t;

typedef union convert {
  stm_word_t w;
  uint8_t b[sizeof(stm_word_t)];
} convert_t;

static void sanity_checks(void)
{
  COMPILE_TIME_ASSERT(sizeof(convert_64_t) == 8);
  COMPILE_TIME_ASSERT(sizeof(convert_32_t) == 4);
  COMPILE_TIME_ASSERT(sizeof(stm_word_t) == 4 || sizeof(stm_word_t) == 8);
  COMPILE_TIME_ASSERT(sizeof(char) == 1);
  COMPILE_TIME_ASSERT(sizeof(short) == 2);
  COMPILE_TIME_ASSERT(sizeof(int) == 4);
  COMPILE_TIME_ASSERT(sizeof(long) == 4 || sizeof(long) == 8);
  COMPILE_TIME_ASSERT(sizeof(float) == 4);
  COMPILE_TIME_ASSERT(sizeof(double) == 8);
}

/* ################################################################### *
 * INLINE LOADS
 * ################################################################### */

static INLINE
uint32_t int_stm_load_t_u32(const uint32_t *addr, const uintptr_t tag)
{
  if (unlikely(((uintptr_t)addr & 0x03) != 0)) {
    // FIXME: not implemented
    abort();
  } else if (sizeof(stm_word_t) == 4) {
    return (uint32_t)TM_LOAD_TAG((const stm_word_t *)addr, tag);
  } else {
    convert_64_t val;
    val.u64 = (uint64_t)TM_LOAD_TAG((const stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x07), tag);
    return val.u32[((uintptr_t)addr & 0x07) >> 2];
  }
}

static INLINE
uint64_t int_stm_load_t_u64(const uint64_t *addr, const uintptr_t tag)
{
  if (unlikely(((uintptr_t)addr & 0x07) != 0)) {
    // FIXME: not implemented
    abort();
  } else if (sizeof(stm_word_t) == 4) {
    convert_64_t val;
    val.u32[0] = (uint32_t)TM_LOAD_TAG((const stm_word_t *)addr, tag);
    val.u32[1] = (uint32_t)TM_LOAD_TAG((const stm_word_t *)addr + 1, tag);
    return val.u64;
  } else {
    return (uint64_t)TM_LOAD_TAG((const stm_word_t *)addr, tag);
  }
}

static INLINE
int int_stm_load_uv_u32(const stm_read_t r, uint32_t *value, int (* const f)(const stm_read_t, stm_word_t *))
{
  if (sizeof(stm_word_t) == 4) {
    return f(r, (stm_word_t *)value);
  } else {
    convert_64_t val;
    const int ret = f(r, (stm_word_t *)&val.u64);
    if (ret)
      *value = val.u32[(((uintptr_t)stm_get_load_addr(r)) & 0x07) >> 2];
    return ret;
  }
}

static INLINE
int int_stm_load_uv_u64(const stm_read_t r, uint64_t *value, int (* const f)(const stm_read_t, stm_word_t *))
{
  if (sizeof(stm_word_t) == 4) {
    // FIXME: not implemented
    abort();
  } else {
    return f(r, (stm_word_t *)value);
  }
}

static INLINE
uint8_t int_stm_load_u8(const uint8_t *addr)
{
  if (sizeof(stm_word_t) == 4) {
    convert_32_t val;
    val.u32 = (uint32_t)TM_LOAD((const stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x03));
    return val.u8[(uintptr_t)addr & 0x03];
  } else {
    convert_64_t val;
    val.u64 = (uint64_t)TM_LOAD((const stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x07));
    return val.u8[(uintptr_t)addr & 0x07];
  }
}

static INLINE
uint16_t int_stm_load_u16(const uint16_t *addr)
{
  if (unlikely(((uintptr_t)addr & 0x01) != 0)) {
    uint16_t val;
    stm_load_bytes((uint8_t *)addr, (uint8_t *)&val, sizeof(uint16_t));
    return val;
  } else if (sizeof(stm_word_t) == 4) {
    convert_32_t val;
    val.u32 = (uint32_t)TM_LOAD((const stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x03));
    return val.u16[((uintptr_t)addr & 0x03) >> 1];
  } else {
    convert_64_t val;
    val.u64 = (uint64_t)TM_LOAD((const stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x07));
    return val.u16[((uintptr_t)addr & 0x07) >> 1];
  }
}

static INLINE
uint32_t int_stm_load_u32(const uint32_t *addr)
{
  if (unlikely(((uintptr_t)addr & 0x03) != 0)) {
    uint32_t val;
    stm_load_bytes((const uint8_t *)addr, (uint8_t *)&val, sizeof(uint32_t));
    return val;
  } else if (sizeof(stm_word_t) == 4) {
    return (uint32_t)TM_LOAD((const stm_word_t *)addr);
  } else {
    convert_64_t val;
    val.u64 = (uint64_t)TM_LOAD((const stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x07));
    return val.u32[((uintptr_t)addr & 0x07) >> 2];
  }
}

static INLINE
uint64_t int_stm_load_u64(const uint64_t *addr)
{
  if (unlikely(((uintptr_t)addr & 0x07) != 0)) {
    uint64_t val;
    stm_load_bytes((uint8_t *)addr, (uint8_t *)&val, sizeof(uint64_t));
    return val;
  } else if (sizeof(stm_word_t) == 4) {
    convert_64_t val;
    val.u32[0] = (uint32_t)TM_LOAD((const stm_word_t *)addr);
    val.u32[1] = (uint32_t)TM_LOAD((const stm_word_t *)addr + 1);
    return val.u64;
  } else {
    return (uint64_t)TM_LOAD((const stm_word_t *)addr);
  }
}

/* ################################################################### *
 * LOADS
 * ################################################################### */

_CALLCONV void *stm_load_tag_ptr(const void **addr, const uintptr_t tag)
{
  union { stm_word_t w; void *v; } convert;
  convert.w = TM_LOAD_TAG((const stm_word_t *)addr, tag);
  return convert.v;
}

_CALLCONV float stm_load_tag_float(const float *addr, const uintptr_t tag)
{
  convert_32_t val;
  val.u32 = int_stm_load_t_u32((const uint32_t *)addr, tag);
  return val.f;
}

_CALLCONV double stm_load_tag_double(const double *addr, const uintptr_t tag)
{
  convert_64_t val;
  val.u64 = int_stm_load_t_u64((const uint64_t *)addr, tag);
  return val.d;
}

_CALLCONV int stm_load_update_ptr(const stm_read_t r, void **value)
{
  union { stm_word_t w; void *v; } convert;
  const int ret = TM_LOAD_UPDATE(r, &convert.w);
  if (ret)
    *value = convert.v;
  return ret;
}

_CALLCONV int stm_load_update_float(const stm_read_t r, float *value)
{
  convert_32_t val;
  const int ret = int_stm_load_uv_u32(r, &val.u32, TM_LOAD_UPDATE);
  if (ret)
    *value = val.f;
  return ret;
}

_CALLCONV int stm_load_update_double(const stm_read_t r, double *value)
{
  convert_64_t val;
  const int ret = int_stm_load_uv_u64(r, &val.u64, TM_LOAD_UPDATE);
  if (ret)
    *value = val.d;
  return ret;
}

_CALLCONV int stm_load_value_ptr(const stm_read_t r, void **value)
{
  union { stm_word_t w; void *v; } convert;
  const int ret = TM_LOAD_VALUE(r, &convert.w);
  if (ret)
    *value = convert.v;
  return ret;
}

_CALLCONV int stm_load_value_float(const stm_read_t r, float *value)
{
  convert_32_t val;
  const int ret = int_stm_load_uv_u32(r, &val.u32, TM_LOAD_VALUE);
  if (ret)
    *value = val.f;
  return ret;
}

_CALLCONV int stm_load_value_double(const stm_read_t r, double *value)
{
  convert_64_t val;
  const int ret = int_stm_load_uv_u64(r, &val.u64, TM_LOAD_VALUE);
  if (ret)
    *value = val.d;
  return ret;
}

_CALLCONV uint8_t stm_load_u8(const uint8_t *addr)
{
  return int_stm_load_u8(addr);
}

_CALLCONV uint16_t stm_load_u16(const uint16_t *addr)
{
  return int_stm_load_u16(addr);
}

_CALLCONV uint32_t stm_load_u32(const uint32_t *addr)
{
  return int_stm_load_u32(addr);
}

_CALLCONV uint64_t stm_load_u64(const uint64_t *addr)
{
  return int_stm_load_u64(addr);
}

_CALLCONV char stm_load_char(const char *addr)
{
  convert_8_t val;
  val.u8 = int_stm_load_u8((const uint8_t *)addr);
  return val.s8;
}

_CALLCONV unsigned char stm_load_uchar(const unsigned char *addr)
{
  return (unsigned char)int_stm_load_u8((const uint8_t *)addr);
}

_CALLCONV short stm_load_short(const short *addr)
{
  convert_16_t val;
  val.u16 = int_stm_load_u16((const uint16_t *)addr);
  return val.s16;
}

_CALLCONV unsigned short stm_load_ushort(const unsigned short *addr)
{
  return (unsigned short)int_stm_load_u16((const uint16_t *)addr);
}

_CALLCONV int stm_load_int(const int *addr)
{
  convert_32_t val;
  val.u32 = int_stm_load_u32((const uint32_t *)addr);
  return val.s32;
}

_CALLCONV unsigned int stm_load_uint(const unsigned int *addr)
{
  return (unsigned int)int_stm_load_u32((const uint32_t *)addr);
}

_CALLCONV long stm_load_long(const long *addr)
{
  if (sizeof(long) == 4) {
    convert_32_t val;
    val.u32 = int_stm_load_u32((const uint32_t *)addr);
    return val.s32;
  } else {
    convert_64_t val;
    val.u64 = int_stm_load_u64((const uint64_t *)addr);
    return val.s64;
  }
}

_CALLCONV unsigned long stm_load_ulong(const unsigned long *addr)
{
  if (sizeof(long) == 4) {
    return (unsigned long)int_stm_load_u32((const uint32_t *)addr);
  } else {
    return (unsigned long)int_stm_load_u64((const uint64_t *)addr);
  }
}

_CALLCONV long stm_load_llong(const long long *addr)
{
  convert_64_t val;
  val.u64 = int_stm_load_u64((const uint64_t *)addr);
  return val.s64;
}

_CALLCONV unsigned long stm_load_ullong(const unsigned long long *addr)
{
  return (unsigned long)int_stm_load_u64((const uint64_t *)addr);
}


_CALLCONV float stm_load_float(const float *addr)
{
  convert_32_t val;
  val.u32 = int_stm_load_u32((const uint32_t *)addr);
  return val.f;
}

_CALLCONV double stm_load_double(const double *addr)
{
  convert_64_t val;
  val.u64 = int_stm_load_u64((const uint64_t *)addr);
  return val.d;
}

_CALLCONV void *stm_load_ptr(const void **addr)
{
  union { stm_word_t w; void *v; } convert;
  convert.w = TM_LOAD((stm_word_t *)addr);
  return convert.v;
}

_CALLCONV void stm_load_bytes(const uint8_t *addr, uint8_t *buf, size_t size)
{
  convert_t val;
  unsigned int i;
  const stm_word_t *a;

  if (size == 0)
    return;
  i = (uintptr_t)addr & (sizeof(stm_word_t) - 1);
  if (i != 0) {
    /* First bytes */
    a = (const stm_word_t *)((uintptr_t)addr & ~(uintptr_t)(sizeof(stm_word_t) - 1));
    val.w = TM_LOAD(a++);
    for (; i < sizeof(stm_word_t) && size > 0; i++, size--)
      *buf++ = val.b[i];
  } else
    a = (const stm_word_t *)addr;
  /* Full words */
  while (size >= sizeof(stm_word_t)) {
#ifdef ALLOW_MISALIGNED_ACCESSES
    *((stm_word_t *)buf) = TM_LOAD(a++);
    buf += sizeof(stm_word_t);
#else /* ! ALLOW_MISALIGNED_ACCESSES */
    val.w = TM_LOAD(a++);
    for (i = 0; i < sizeof(stm_word_t); i++)
      *buf++ = val.b[i];
#endif /* ! ALLOW_MISALIGNED_ACCESSES */
    size -= sizeof(stm_word_t);
  }
  if (size > 0) {
    /* Last bytes */
    val.w = TM_LOAD(a);
    i = 0;
    for (i = 0; size > 0; i++, size--)
      *buf++ = val.b[i];
  }
}

/* ################################################################### *
 * INLINE STORES
 * ################################################################### */

static INLINE
int int_stm_store_update_u32(const stm_write_t w, const uint32_t value)
{
  if (sizeof(stm_word_t) == 4) {
    return TM_STORE_UPDATE(w, (stm_word_t)value);
  } else {
    uintptr_t addr = (uintptr_t)stm_get_store_addr(w);
    convert_64_t val, mask;
    val.u32[(addr & 0x07) >> 2] = value;
    mask.u64 = 0;
    mask.u32[(addr & 0x07) >> 2] = ~(uint32_t)0;
    return TM_STORE2_UPDATE(w, (stm_word_t)val.u64, (stm_word_t)mask.u64);
  }
}

static INLINE
int int_stm_store_update_u64(const stm_write_t w, const uint64_t value)
{
  if (sizeof(stm_word_t) == 4) {
    // FIXME: not implemented
    abort();
  } else {
    return TM_STORE_UPDATE(w, (stm_word_t)value);
  }
}

static INLINE
int int_stm_store_value_u32(const stm_write_t w, uint32_t *value)
{
  if (sizeof(stm_word_t) == 4) {
    return TM_STORE_VALUE(w, (stm_word_t *)value);
  } else {
    convert_64_t val;
    const int ret = TM_STORE_VALUE(w, (stm_word_t *)&val.u64);
    if (ret)
      *value = val.u32[((uintptr_t)(stm_get_store_addr(w)) & 0x07) >> 2];
    return ret;
  }
}

static INLINE
int int_stm_store_value_u64(const stm_write_t w, uint64_t *value)
{
  if (sizeof(stm_word_t) == 4) {
    // FIXME: not implemented
    abort();
  } else {
    return TM_STORE_VALUE(w, (stm_word_t *)value);
  }
}

static INLINE
void int_stm_store_u8(uint8_t *addr, uint8_t value)
{
  if (sizeof(stm_word_t) == 4) {
    convert_32_t val, mask;
    val.u8[(uintptr_t)addr & 0x03] = value;
    mask.u32 = 0;
    mask.u8[(uintptr_t)addr & 0x03] = ~(uint8_t)0;
    TM_STORE2((stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x03), (stm_word_t)val.u32, (stm_word_t)mask.u32);
  } else {
    convert_64_t val, mask;
    val.u8[(uintptr_t)addr & 0x07] = value;
    mask.u64 = 0;
    mask.u8[(uintptr_t)addr & 0x07] = ~(uint8_t)0;
    TM_STORE2((stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x07), (stm_word_t)val.u64, (stm_word_t)mask.u64);
  }
}

static INLINE
void int_stm_store_u16(uint16_t *addr, uint16_t value)
{
  if (unlikely(((uintptr_t)addr & 0x01) != 0)) {
    stm_store_bytes((uint8_t *)addr, (uint8_t *)&value, sizeof(uint16_t));
  } else if (sizeof(stm_word_t) == 4) {
    convert_32_t val, mask;
    val.u16[((uintptr_t)addr & 0x03) >> 1] = value;
    mask.u32 = 0;
    mask.u16[((uintptr_t)addr & 0x03) >> 1] = ~(uint16_t)0;
    TM_STORE2((stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x03), (stm_word_t)val.u32, (stm_word_t)mask.u32);
  } else {
    convert_64_t val, mask;
    val.u16[((uintptr_t)addr & 0x07) >> 1] = value;
    mask.u64 = 0;
    mask.u16[((uintptr_t)addr & 0x07) >> 1] = ~(uint16_t)0;
    TM_STORE2((stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x07), (stm_word_t)val.u64, (stm_word_t)mask.u64);
  }
}

static INLINE
void int_stm_store_u32(uint32_t *addr, uint32_t value)
{
  if (unlikely(((uintptr_t)addr & 0x03) != 0)) {
    stm_store_bytes((uint8_t *)addr, (uint8_t *)&value, sizeof(uint32_t));
  } else if (sizeof(stm_word_t) == 4) {
    TM_STORE((stm_word_t *)addr, (stm_word_t)value);
  } else {
    convert_64_t val, mask;
    val.u32[((uintptr_t)addr & 0x07) >> 2] = value;
    mask.u64 = 0;
    mask.u32[((uintptr_t)addr & 0x07) >> 2] = ~(uint32_t)0;
    TM_STORE2((stm_word_t *)((uintptr_t)addr & ~(uintptr_t)0x07), (stm_word_t)val.u64, (stm_word_t)mask.u64);
  }
}

static INLINE
void int_stm_store_u64(uint64_t *addr, uint64_t value)
{
  if (unlikely(((uintptr_t)addr & 0x07) != 0)) {
    stm_store_bytes((uint8_t *)addr, (uint8_t *)&value, sizeof(uint64_t));
  } else if (sizeof(stm_word_t) == 4) {
    convert_64_t val;
    val.u64 = value;
    TM_STORE((stm_word_t *)addr, (stm_word_t)val.u32[0]);
    TM_STORE((stm_word_t *)addr + 1, (stm_word_t)val.u32[1]);
  } else {
    return TM_STORE((stm_word_t *)addr, (stm_word_t)value);
  }
}

/* ################################################################### *
 * STORES
 * ################################################################### */

_CALLCONV int stm_store_update_ptr(const stm_write_t w, const void *value)
{
  union { const stm_word_t w; const void *v; } convert;
  convert.v = value;
  return TM_STORE_UPDATE(w, convert.w);
}

_CALLCONV int stm_store_update_float(const stm_write_t w, const float value)
{
  convert_32_t val;
  val.f = value;
  return int_stm_store_update_u32(w, val.u32);
}

_CALLCONV int stm_store_update_double(const stm_write_t w, const double value)
{
  convert_64_t val;
  val.d = value;
  return int_stm_store_update_u64(w, val.u64);
}

_CALLCONV int stm_store_value_ptr(const stm_write_t w, void **value)
{
  union { stm_word_t w; void *v; } convert;
  const int ret = TM_STORE_VALUE(w, &convert.w);
  if (ret)
    *value = convert.v;
  return ret;
}

_CALLCONV int stm_store_value_float(const stm_write_t w, float *value)
{
  convert_32_t val;
  const int ret = int_stm_store_value_u32(w, &val.u32);
  if (ret)
    *value = val.f;
  return ret;
}

_CALLCONV int stm_store_value_double(const stm_write_t w, double *value)
{
  convert_64_t val;
  const int ret = int_stm_store_value_u64(w, &val.u64);
  if (ret)
    *value = val.d;
  return ret;
}

_CALLCONV void stm_store_u8(uint8_t *addr, uint8_t value)
{
  int_stm_store_u8(addr, value);
}

_CALLCONV void stm_store_u16(uint16_t *addr, uint16_t value)
{
  int_stm_store_u16(addr, value);
}

_CALLCONV void stm_store_u32(uint32_t *addr, uint32_t value)
{
  int_stm_store_u32(addr, value);
}

_CALLCONV void stm_store_u64(uint64_t *addr, uint64_t value)
{
  int_stm_store_u64(addr, value);
}

_CALLCONV void stm_store_char(char *addr, char value)
{
  convert_8_t val;
  val.s8 = value;
  int_stm_store_u8((uint8_t *)addr, val.u8);
}

_CALLCONV void stm_store_uchar(unsigned char *addr, unsigned char value)
{
  int_stm_store_u8((uint8_t *)addr, (uint8_t)value);
}

_CALLCONV void stm_store_short(short *addr, short value)
{
  convert_16_t val;
  val.s16 = value;
  int_stm_store_u16((uint16_t *)addr, val.u16);
}

_CALLCONV void stm_store_ushort(unsigned short *addr, unsigned short value)
{
  int_stm_store_u16((uint16_t *)addr, (uint16_t)value);
}

_CALLCONV void stm_store_int(int *addr, int value)
{
  convert_32_t val;
  val.s32 = value;
  int_stm_store_u32((uint32_t *)addr, val.u32);
}

_CALLCONV void stm_store_uint(unsigned int *addr, unsigned int value)
{
  int_stm_store_u32((uint32_t *)addr, (uint32_t)value);
}

_CALLCONV void stm_store_long(long *addr, long value)
{
  if (sizeof(long) == 4) {
    convert_32_t val;
    val.s32 = value;
    int_stm_store_u32((uint32_t *)addr, val.u32);
  } else {
    convert_64_t val;
    val.s64 = value;
    int_stm_store_u64((uint64_t *)addr, val.u64);
  }
}

_CALLCONV void stm_store_ulong(unsigned long *addr, unsigned long value)
{
  if (sizeof(long) == 4) {
    int_stm_store_u32((uint32_t *)addr, (uint32_t)value);
  } else {
    int_stm_store_u64((uint64_t *)addr, (uint64_t)value);
  }
}

_CALLCONV void stm_store_llong(long long *addr, long long value)
{
  convert_64_t val;
  val.s64 = value;
  int_stm_store_u64((uint64_t *)addr, val.u64);
}

_CALLCONV void stm_store_ullong(unsigned long long *addr, unsigned long long value)
{
  int_stm_store_u64((uint64_t *)addr, (uint64_t)value);
}

_CALLCONV void stm_store_float(float *addr, const float value)
{
  convert_32_t val;
  val.f = value;
  int_stm_store_u32((uint32_t *)addr, val.u32);
}

_CALLCONV void stm_store_double(double *addr, double value)
{
  convert_64_t val;
  val.d = value;
  int_stm_store_u64((uint64_t *)addr, val.u64);
}

_CALLCONV void stm_store_ptr(void **addr, const void *value)
{
  union { const stm_word_t w; const void *v; } convert;
  convert.v = value;
  TM_STORE((stm_word_t *)addr, convert.w);
}

_CALLCONV void stm_store_bytes(uint8_t *addr, uint8_t *buf, size_t size)
{
  convert_t val, mask;
  unsigned int i;
  stm_word_t *a;

  if (size == 0)
    return;
  i = (uintptr_t)addr & (sizeof(stm_word_t) - 1);
  if (i != 0) {
    /* First bytes */
    a = (stm_word_t *)((uintptr_t)addr & ~(uintptr_t)(sizeof(stm_word_t) - 1));
    val.w = mask.w = 0;
    for (; i < sizeof(stm_word_t) && size > 0; i++, size--) {
      mask.b[i] = 0xFF;
      val.b[i] = *buf++;
    }
    TM_STORE2(a++, val.w, mask.w);
  } else
    a = (stm_word_t *)addr;
  /* Full words */
  while (size >= sizeof(stm_word_t)) {
#ifdef ALLOW_MISALIGNED_ACCESSES
    TM_STORE(a++, *((stm_word_t *)buf));
    buf += sizeof(stm_word_t);
#else /* ! ALLOW_MISALIGNED_ACCESSES */
    for (i = 0; i < sizeof(stm_word_t); i++)
      val.b[i] = *buf++;
    TM_STORE(a++, val.w);
#endif /* ! ALLOW_MISALIGNED_ACCESSES */
    size -= sizeof(stm_word_t);
  }
  if (size > 0) {
    /* Last bytes */
    val.w = mask.w = 0;
    for (i = 0; size > 0; i++, size--) {
      mask.b[i] = 0xFF;
      val.b[i] = *buf++;
    }
    TM_STORE2(a, val.w, mask.w);
  }
}

_CALLCONV void stm_set_bytes(uint8_t *addr, uint8_t byte, size_t count)
{
  convert_t val, mask;
  unsigned int i;
  stm_word_t *a;

  if (count == 0)
    return;

  for (i = 0; i < sizeof(stm_word_t); i++)
    val.b[i] = byte;

  i = (uintptr_t)addr & (sizeof(stm_word_t) - 1);
  if (i != 0) {
    /* First bytes */
    a = (stm_word_t *)((uintptr_t)addr & ~(uintptr_t)(sizeof(stm_word_t) - 1));
    mask.w = 0;
    for (; i < sizeof(stm_word_t) && count > 0; i++, count--)
      mask.b[i] = 0xFF;
    TM_STORE2(a++, val.w, mask.w);
  } else
    a = (stm_word_t *)addr;
  /* Full words */
  while (count >= sizeof(stm_word_t)) {
    TM_STORE(a++, val.w);
    count -= sizeof(stm_word_t);
  }
  if (count > 0) {
    /* Last bytes */
    mask.w = 0;
    for (i = 0; count > 0; i++, count--)
      mask.b[i] = 0xFF;
    TM_STORE2(a, val.w, mask.w);
  }
}

#undef TM_LOAD
#undef TM_STORE
#undef TM_STORE2

