/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/expr_maps.h"

namespace lean {
class substitution;
class metavar_generator;
/**
    \brief Return a new placeholder expression. To be able to track location,
    a new constant for each placeholder.
*/
expr mk_placholder();

/**
    \brief Return true iff the given expression is a placeholder.
*/
bool is_placeholder(expr const & e);

/**
    \brief Return true iff the given expression contains placeholders.
*/
bool has_placeholder(expr const & e);

/**
   \brief Replace the placeholders in \c e with fresh metavariables from \c mgen.
   if \c trace is not null, then for each new expression \c t created based on
   \c s, we store <tt>(*trace)[t] = s</tt>. We say this is traceability information.
*/
expr replace_placeholders_with_metavars(expr const & e, metavar_generator & mgen, expr_map<expr> * trace = nullptr);
}
