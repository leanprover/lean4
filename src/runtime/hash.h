/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lean/lean.h>
#include "runtime/debug.h"
#include "runtime/int.h"

namespace lean {

uint64 hash_str(size_t len, unsigned char const * str, uint64 init_value);

inline uint64 hash(uint64 h, uint64 k) {
    return lean_uint64_mix_hash(h, k);
}

}
