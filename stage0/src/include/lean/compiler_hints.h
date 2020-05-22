/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once

#if defined(__GNUC__) || defined(__clang__)
#define LEAN_UNLIKELY(x) (__builtin_expect((x), 0))
#define LEAN_LIKELY(x) (__builtin_expect((x), 1))
#define LEAN_ALWAYS_INLINE __attribute__((always_inline))
#else
#define LEAN_UNLIKELY(x) (x)
#define LEAN_LIKELY(x) (x)
#define LEAN_ALWAYS_INLINE
#endif
