/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
/** \brief Given an inductive datatype \c n, store in \c r a "bitvector" s.t.
    r[i][j] is true iff the j-th argument of the i-th minor premise of the recursor \c n.rec
    is a recursive argument.
    \pre inductive::is_inductive_decl(env, n)
*/
void get_rec_args(environment const & env, name const & n, buffer<buffer<bool>> & r);

/** \brief Return true iff \c e is of the form <tt>(C.rec ...)</tt> and is recursive.
    That is, \c C is a recursive inductive datatype, \c C is *not* an inductive predicate,
    and at least one minor premise uses a recursive argument.
*/
bool is_recursive_rec_app(environment const & env, expr const & e);
}
