/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
namespace blast {
/** \brief Put the given expression in weak-head-normal-form with respect to the
    current state being processed by the blast tactic. */
expr whnf(expr const & e);
/** \brief Return the type of the given expression with respect to the current state being
    processed by the blast tactic.

    \remark: (potential side-effect) this procedure may update the meta-variable assignment
    associated with the current state. */
expr infer_type(expr const & e);
/** \brief Return true if \c e is a Proposition */
bool is_prop(expr const & e);
/** \brief Return true iff the two expressions are definitionally equal in the
    current state being processed by the blast tactic.

    \remark: (potential side-effect) this procedure may update the meta-variable assignment
    associated with the current state. */
bool is_def_eq(expr const & e1, expr const & e2);
bool is_def_eq(level const & l1, level const & l2);
bool is_def_eq(levels const & l1, levels const & l2);
}}
