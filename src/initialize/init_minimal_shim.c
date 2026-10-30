/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/

/* Linked into an executable ahead of `libleanshared`, this redirects the `lean_initialize` calls of
its generated module initializers to `lean_initialize_minimal`. Plain C so that the executable does
not need the C++ runtime. */
void lean_initialize_minimal(void);

void lean_initialize(void) {
    lean_initialize_minimal();
}
