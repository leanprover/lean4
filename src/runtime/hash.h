/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "runtime/debug.h"
#include "runtime/int.h"

namespace lean {

uint64 hash_str(size_t len, unsigned char const * str, uint64 init_value);

inline uint64 hash(uint64 h, uint64 k) {
    uint64 m = 0xc6a4a7935bd1e995;
    uint64 r = 47;
    k *= m;
    k ^= k >> r;
    k ^= m;
    h ^= k;
    h *= m;
    return h;
}

}
