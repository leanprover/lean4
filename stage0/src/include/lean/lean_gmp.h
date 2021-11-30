/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <gmp.h>
#include <lean/lean.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifdef LEAN_USE_GMP
LEAN_SHARED lean_object * lean_alloc_mpz(mpz_t);
/* Set `v` with the value stored in `o`.
   - pre: `lean_is_mpz(o)`
   - pre: `v` has already been initialized using `mpz_init` (or equivalent).
*/
LEAN_SHARED void lean_extract_mpz_value(lean_object * o, mpz_t v);
#endif

#ifdef __cplusplus
}
#endif
