/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/io_state.h"
#include "kernel/kernel_decls.h"

namespace lean {
// See src/builtin/kernel.lean for signatures.
extern expr const TypeU;

/** \brief Return the Lean Boolean type. */
expr mk_bool_type();
extern expr const Bool;
bool is_bool(expr const & e);

/** \brief Create a Lean Boolean value (true/false) */
expr mk_bool_value(bool v);
extern expr const True;
extern expr const False;
/** \brief Return true iff \c e is a Lean Boolean value. */
bool is_bool_value(expr const & e);
/**
    \brief Convert a Lean Boolean value into a C++ Boolean value.
    \pre is_bool_value(e)
*/
bool to_bool(expr const & e);
/** \brief Return true iff \c e is the Lean true value. */
bool is_true(expr const & e);
/** \brief Return true iff \c e is the Lean false value. */
bool is_false(expr const & e);

inline expr Implies(expr const & e1, expr const & e2) { return mk_implies(e1, e2); }
inline expr And(expr const & e1, expr const & e2) { return mk_and(e1, e2); }
inline expr Or(expr const & e1, expr const & e2) { return mk_or(e1, e2); }
inline expr Not(expr const & e) { return mk_not(e); }
inline expr Exists(expr const & A, expr const & P) { return mk_exists(A, P); }
// inline expr hEq(expr const & A, expr const & l, expr const & r) { return mk_eq(A, l, r); }

void import_kernel(environment const & env, io_state const & ios);
}
