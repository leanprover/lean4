/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/expr_maps.h"

namespace lean {
class metavar_env;
/**
    \brief Return a new placeholder expression (with an optional
    type). To be able to track location, a new constant for each
    placeholder.
*/
expr mk_placeholder(optional<expr> const & t = none_expr());

/**
    \brief Return true iff the given expression is a placeholder.
*/
bool is_placeholder(expr const & e);

/**
    \brief Return true iff the given expression contains placeholders.
*/
bool has_placeholder(expr const & e);

/**
   \brief Replace the placeholders in \c e with fresh metavariables from \c menv.
   if \c new2old is not nullptr, then for each new expression \c t created based on
   \c s, we store <tt>(*new2old)[t] = s</tt>.
*/
expr replace_placeholders_with_metavars(expr const & e, metavar_env const & menv, expr_map<expr> * new2old = nullptr);
}
