/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"

namespace lean {
typedef name_map<expr>      substitutions;

/* \brief Given `e`, for each (x := v) in `s` replace `x` with `v` in `e` */
expr apply_substitutions(expr const & e, substitutions const & s);
list<expr> apply_substitutions(list<expr> const & es, substitutions const & s);

/* \brief Return a new set of substitutions containing (x := apply_substitutions(v, s2)) for
   each (x := v) in `s1`. */
substitutions apply_substitutions(substitutions const & s1, substitutions const & s2);

/* \brief Return a new set of substitutions containing the entries of `s1` and `s2`. */
substitutions merge(substitutions const & s1, substitutions const & s2);

/** \brief Given (H : lhs = rhs), replace lhs with rhs in the goal \c mvar. If symm == true, then replace rhs with lhs.
    The replaced term must be a local constant. If substs is not nullptr, then hypotheses renamed by revert/intro
    are stored in \c substs, and the actual substitution.

    \pre is_metavar(mvar)
    \pre is_local(H)
    \pre mctx.get_metavar_decl(mvar) != none
    \pre typeof(H) is an equality
    \pre symm == false ==> is_local(lhs(typeof(H)))
    \pre symm == false ==> is_local(rhs(typeof(H))) */
expr subst(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
           expr const & mvar, expr const & H, bool symm, substitutions * substs);

void initialize_subst_tactic();
void finalize_subst_tactic();
}
