/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "kernel/expr.h"

namespace lean {
class ro_metavar_env;
/** \brief Replace the loose bound variables with indices 0, ..., n-1 with s[0], ..., s[n-1] in e. */
expr instantiate(expr const & e, unsigned n, expr const * s);
expr instantiate(expr const & e, std::initializer_list<expr> const & l);
/** \brief Replace loose bound variable \c i with \c s in \c e. */
expr instantiate(expr const & e, unsigned i, expr const & s);
/** \brief Replace loose bound variable \c 0 with \c s in \c e. */
expr instantiate(expr const & e, expr const & s);

/** \brief Replace the free variables with indices 0, ..., n-1 with s[n-1], ..., s[0] in e. */
expr instantiate_rev(expr const & e, unsigned n, expr const * s);
inline expr instantiate_rev(expr const & e, buffer<expr> const & s) {
    return instantiate_rev(e, s.size(), s.data());
}

expr apply_beta(expr f, unsigned num_rev_args, expr const * rev_args, bool preserve_data = true, bool zeta = false);
bool is_head_beta(expr const & t);
expr head_beta_reduce(expr const & t);
/* If `e` is of the form `(fun x, t) a` return `head_beta_const_fn(t)` if `t` does not depend on `x`,
   and `e` otherwise. We also reduce `(fun x_1 ... x_n, x_i) a_1 ... a_n` into `a_[n-i-1]` */
expr cheap_beta_reduce(expr const & e);

/** \brief Instantiate the universe level parameters \c ps occurring in \c e with the levels \c ls.
    \pre length(ps) == length(ls) */
expr instantiate_lparams(expr const & e, names const & ps, levels const & ls);

class constant_info;
/** \brief Instantiate the universe level parameters of the type of the given constant.
    \pre d.get_num_lparams() == length(ls) */
expr instantiate_type_lparams(constant_info const & info, levels const & ls);
/** \brief Instantiate the universe level parameters of the value of the given constant.
    \pre d.get_num_lparams() == length(ls) */
expr instantiate_value_lparams(constant_info const & info, levels const & ls);
}
