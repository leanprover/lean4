/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <stdint.h>
#include <cstddef>
namespace lean {

typedef int8_t  int8;
typedef uint8_t uint8;
static_assert(sizeof(int8) == 1,  "unexpected int8 size");  // NOLINT
static_assert(sizeof(uint8) == 1, "unexpected uint8 size"); // NOLINT
                                                              //
typedef int16_t  int16;
typedef uint16_t uint16;
static_assert(sizeof(int16) == 2,  "unexpected int16 size");  // NOLINT
static_assert(sizeof(uint16) == 2, "unexpected uint16 size"); // NOLINT
                                                              //
typedef int32_t  int32;
typedef uint32_t uint32;
static_assert(sizeof(int32) == 4,  "unexpected int32 size");  // NOLINT
static_assert(sizeof(uint32) == 4, "unexpected uint32 size"); // NOLINT

typedef int64_t  int64;
typedef uint64_t uint64;
static_assert(sizeof(int64) == 8,  "unexpected int64 size");  // NOLINT
static_assert(sizeof(uint64) == 8, "unexpected uint64 size"); // NOLINT
                                                              //
typedef size_t usize;
typedef ptrdiff_t isize;
static_assert(sizeof(usize) == sizeof(isize), "unexpected size difference usize/isize");   // NOLINT
static_assert(sizeof(usize) == 4 || sizeof(usize) == 8, "usize is neither 32 nor 64 bit"); // NOLINT
                                                                                           //

}
