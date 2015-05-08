/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name.h"
#include "kernel/constraint.h"

namespace lean {
class environment;
class delayed_justification;

/**
   \brief Extension context (aka API provided to macro_definitions and normalizer_extensions).
   The extension can request
   1) the environment being used.
   2) the weak head normal form of an expression.
   3) the type of an expression.
   4) a new fresh name.
   5) registration of a new constraint.
*/
class extension_context {
public:
    virtual ~extension_context() {}
    virtual environment const & env() const = 0;
    virtual pair<expr, constraint_seq> whnf(expr const & e) = 0;
    virtual pair<bool, constraint_seq> is_def_eq(expr const & e1, expr const & e2, delayed_justification & j) = 0;
    virtual pair<expr, constraint_seq> check_type(expr const & e, bool infer_only) = 0;
    virtual optional<expr> is_stuck(expr const & e) = 0;
    virtual name mk_fresh_name() = 0;
    expr check_type(expr const & e, constraint_seq & cs, bool infer_only);
    expr whnf(expr const & e, constraint_seq & cs);
    pair<expr, constraint_seq> infer(expr const & e);
    expr infer_type(expr const & e, constraint_seq & cs);
    bool is_def_eq(expr const & e1, expr const & e2, delayed_justification & j, constraint_seq & cs);
};
}
