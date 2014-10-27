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
expr normalize(environment const & env, expr const & e);
expr normalize(environment const & env, level_param_names const & ls, expr const & e);
/** \brief Similar to <tt>expr normalize(environment const & env, expr const & e)</tt>, but
    uses the converter associated with \c tc. */
expr normalize(type_checker & tc, expr const & e);
/** \brief Return the \c e normal form with respect to \c tc, and store generated constraints
    into \c cs.
*/
expr normalize(type_checker & tc, expr const & e, constraint_seq & cs);
/** \brief Return the \c e normal form with respect to \c tc, and store generated constraints
    into \c cs.

    \remark A sub-expression is evaluated only if \c pred returns true.
*/
expr normalize(type_checker & tc, expr const & e, std::function<bool(expr const&)> const & pred,
               constraint_seq & cs);
}
