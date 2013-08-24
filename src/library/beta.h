/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
#include "name_set.h"

namespace lean {
class environment;
/**
    \brief Return true iff the given expression is of the form:

    ((fun (x : A), B) Arg)
*/
bool is_head_beta(expr const & e);
/** \brief Apply head beta-reduction to the given expression. */
expr head_beta(expr const & e);

/**
   \brief Try to reduce the head of the given expression.
   The following reductions are tried:
   1- Beta reduction
   2- Constant unfolding (if constant is defined in env, and defs ==
   nullptr or it contains constant).
   3- Let expansion
*/
expr head_reduce(expr const & e, environment const & env, name_set const * defs = nullptr);
};
