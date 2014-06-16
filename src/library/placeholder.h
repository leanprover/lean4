/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "kernel/expr.h"

// Placeholders are used to mark locations where additional
// metavariables should be inserted.
namespace lean {
/** \brief Return a new universe level placeholder. */
level mk_level_placeholder();

/** \brief Return a new expression placeholder expression. */
expr mk_expr_placeholder(optional<expr> const & type = none_expr());

/** \brief Return true if the given level is a placeholder. */
bool is_placeholder(level const & e);

/** \brief Return true iff the given expression is a placeholder. */
bool is_placeholder(expr const & e);

/** \brief Return the type of the placeholder (if available) */
optional<expr> placeholder_type(expr const & e);

/** \brief Return true iff the given expression contains placeholders. */
bool has_placeholder(expr const & e);

void open_placeholder(lua_State * L);
}
