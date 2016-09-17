/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

// Placeholders are used to mark locations where additional
// metavariables should be inserted.
namespace lean {
/** \brief Return a new universe level placeholder. */
level mk_level_placeholder();
level mk_level_one_placeholder();

enum class expr_placeholder_kind { Implicit, StrictImplicit, Explicit };
/** \brief Return a new expression placeholder expression. */
expr mk_expr_placeholder(optional<expr> const & type = none_expr(), expr_placeholder_kind k = expr_placeholder_kind::Implicit);
inline expr mk_explicit_expr_placeholder(optional<expr> const & type = none_expr()) {
    return mk_expr_placeholder(type, expr_placeholder_kind::Explicit);
}
inline expr mk_strict_expr_placeholder(optional<expr> const & type = none_expr()) {
    return mk_expr_placeholder(type, expr_placeholder_kind::StrictImplicit);
}

/** \brief Return true if the given level is a placeholder. */
bool is_placeholder(level const & e);
bool is_one_placeholder(level const & e);

/** \brief Return true iff the given expression is a placeholder (strict, explicit or implicit). */
bool is_placeholder(expr const & e);

/** \brief Return true iff the given expression is a strict placeholder. */
bool is_strict_placeholder(expr const & e);

/** \brief Return true iff the given expression is an explicit placeholder. */
bool is_explicit_placeholder(expr const & e);

/** \brief Return the type of the placeholder (if available) */
optional<expr> placeholder_type(expr const & e);

/** \brief Return true iff the given expression contains placeholders. */
bool has_placeholder(expr const & e);

void initialize_placeholder();
void finalize_placeholder();
}
