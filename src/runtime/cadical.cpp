/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Henrik Böving

Bindings to the CaDiCaL SAT solver linked into the Lean libraries.
*/

#include <lean/lean.h>

#ifdef LEAN_CADICAL
#include <cadical.hpp>
#endif

/* Lean.Cadical.signature (u : Unit) : String */
extern "C" LEAN_EXPORT lean_object * lean_cadical_signature(lean_object * /* u */) {
#ifdef LEAN_CADICAL
    return lean_mk_string(CaDiCaL::Solver::signature());
#else
    return lean_mk_string("");
#endif
}
