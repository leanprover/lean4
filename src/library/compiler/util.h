/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/type_checker.h"
#include "library/constants.h"
#include "library/util.h"

namespace lean {
/* If `e` is of the form `(fun x, t) a` return `head_beta_const_fn(t)` if `t` does not depend on `x`,
   and `e` otherwise. We also reduce `(fun x_1 ... x_n, x_i) a_1 ... a_n` into `a_[n-i-1]` */
expr cheap_beta_reduce(expr const & e);

/* Return true if the given argument is mdata relevant to the compiler

   Remark: we currently don't keep any metadata in the compiler. */
inline bool is_lc_mdata(expr const &) { return false; }

bool is_cases_on_recursor(environment const & env, name const & n);
inline bool is_cases_on_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && is_cases_on_recursor(env, const_name(fn));
}

inline bool is_lc_unreachable_app(expr const & e) { return is_app_of(e, get_lc_unreachable_name(), 1); }
inline bool is_lc_proof_app(expr const & e) { return is_app_of(e, get_lc_proof_name(), 1); }
inline bool is_lc_cast_app(expr const & e) { return is_app_of(e, get_lc_cast_name(), 3); }

expr mk_lc_unreachable(type_checker::state & s, local_ctx const & lctx, expr const & type);

/* Create an auxiliary names for a declaration that saves the result of the compilation
   after step simplification. */
inline name mk_cstage1_name(name const & decl_name) {
    return name(decl_name, "_cstage1");
}
}
