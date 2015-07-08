/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "kernel/type_checker.h"

namespace lean {
/** \brief Return the \c e normal form with respect to the environment \c env.
    Any unification constraint generated in the process is discarded.

    \remark Unification constraints are only generated if \c e contains meta-variables.
*/
expr normalize(environment const & env, expr const & e, bool eta = false);
expr normalize(environment const & env, level_param_names const & ls, expr const & e, bool eta = false);
/** \brief Similar to <tt>expr normalize(environment const & env, expr const & e)</tt>, but
    uses the converter associated with \c tc. */
expr normalize(type_checker & tc, expr const & e, bool eta = false);
expr normalize(type_checker & tc, level_param_names const & ls, expr const & e, bool eta = false, bool eval_nested_prop = true);
/** \brief Return the \c e normal form with respect to \c tc, and store generated constraints
    into \c cs.
*/
expr normalize(type_checker & tc, expr const & e, constraint_seq & cs, bool eta = false);
/** \brief Return the \c e normal form with respect to \c tc, and store generated constraints
    into \c cs.

    \remark A sub-expression is evaluated only if \c pred returns true.
*/
expr normalize(type_checker & tc, expr const & e, std::function<bool(expr const&)> const & pred, // NOLINT
               constraint_seq & cs, bool eta = false);

/** \brief [unfold] hint instructs the normalizer (and simplifier) that
    a function application (f a_1 ... a_i ... a_n) should be unfolded
    when argument a_i is a constructor.

    The constant will be unfolded even if it the whnf procedure did not unfolded it.

    Of course, kernel opaque constants are not unfolded.
*/
environment add_unfold_hint(environment const & env, name const & n, list<unsigned> const & idxs, bool persistent = true);
inline environment add_unfold_hint(environment const & env, name const & n, unsigned idx, bool persistent = true) {
    return add_unfold_hint(env, n, to_list(idx), persistent);
}
environment erase_unfold_hint(environment const & env, name const & n, bool persistent = true);
/** \brief Retrieve the hint added with the procedure add_unfold_hint. */
list<unsigned> has_unfold_hint(environment const & env, name const & d);

/** \brief [unfold-full] hint instructs normalizer (and simplifier) that function application
    (f a_1 ... a_n) should be unfolded when it is fully applied */
environment add_unfold_full_hint(environment const & env, name const & n, bool persistent = true);
environment erase_unfold_full_hint(environment const & env, name const & n, bool persistent = true);
/** \brief Retrieve the hint added with the procedure add_unfold_full_hint. */
optional<unsigned> has_unfold_full_hint(environment const & env, name const & d);


/** \brief unfold-m hint instructs normalizer (and simplifier) that function application
    (f ...) should be unfolded when it is the major premise of a constructor like operator */
environment add_constructor_hint(environment const & env, name const & n, bool persistent = true);
environment erase_constructor_hint(environment const & env, name const & n, bool persistent = true);
/** \brief Retrieve the hint added with the procedure add_constructor_hint. */
optional<unsigned> has_constructor_hint(environment const & env, name const & d);

expr try_eta(expr const & e);
expr beta_reduce(expr t);
expr eta_reduce(expr t);
expr beta_eta_reduce(expr t);

void initialize_normalize();
void finalize_normalize();
}
