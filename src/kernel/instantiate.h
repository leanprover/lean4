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
/** \brief Replace the free variables with indices 0, ..., n-1 with s[0], ..., s[n-1] in e. */
expr instantiate(expr const & e, unsigned n, expr const * s);
expr instantiate(expr const & e, std::initializer_list<expr> const & l);
/** \brief Replace free variable \c i with \c s in \c e. */
expr instantiate(expr const & e, unsigned i, expr const & s);
/** \brief Replace free variable \c 0 with \c s in \c e. */
expr instantiate(expr const & e, expr const & s);

/** \brief Replace the free variables with indices 0, ..., n-1 with s[n-1], ..., s[0] in e. */
expr instantiate_rev(expr const & e, unsigned n, expr const * s);
inline expr instantiate_rev(expr const & e, buffer<expr> const & s) {
    return instantiate_rev(e, s.size(), s.data());
}

expr apply_beta(expr f, unsigned num_args, expr const * args);
bool is_head_beta(expr const & t);
expr head_beta_reduce(expr const & t);

/** \brief Instantiate the universe level parameters \c ps occurring in \c e with the levels \c ls.
    \pre length(ps) == length(ls)
*/
expr instantiate_univ_params(expr const & e, level_param_names const & ps, levels const & ls);

class declaration;
/** \brief Instantiate the universe level parameters of the type of the given declaration.
    \pre d.get_num_univ_params() == length(ls)
*/
expr instantiate_type_univ_params(declaration const & d, levels const & ls);
/** \brief Instantiate the universe level parameters of the value of the given declaration.
    \pre d.get_num_univ_params() == length(ls)
*/
expr instantiate_value_univ_params(declaration const & d, levels const & ls);

/** \brief Clear thread local caches used by instantiate_value_univ_params and instantiate_type_univ_params.
    We clear the caches whenever we enable expression caching (aka max sharing).
    We do that because the cache may still contain expressions that are not maximally shared. */
void clear_instantiate_cache();
}
