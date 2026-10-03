/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
*/
#pragma once
#include <cstdint>

namespace lean {
inline unsigned popcount_word(uint64_t n) {
#if defined(__GNUC__) || defined(__clang__)
    // The compiler supplies a portable fallback when the target has no popcount instruction.
    return __builtin_popcountll(n);
#else
    unsigned count = 0;
    while (n) { n &= n - 1; ++count; }
    return count;
#endif
}
}
