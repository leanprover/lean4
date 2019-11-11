/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <stdint.h>
namespace lean {
typedef int64_t  int64;
typedef uint64_t uint64;
static_assert(sizeof(int64) == 8,  "unexpected int64 size");  // NOLINT
static_assert(sizeof(uint64) == 8, "unexpected uint64 size"); // NOLINT
}
