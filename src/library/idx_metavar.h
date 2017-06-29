/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
/** \brief Create a universe level metavariable that can be used as a placeholder in #match.

    \remark The index \c i is encoded in the hierarchical name, and can be quickly accessed.
    In the match procedure the substitution is also efficiently represented as an array (aka buffer).
*/
level mk_idx_metauniv(unsigned i);
/** \brief Return true iff \c l is a metauniverse created using \c mk_idx_metauniv */
bool is_idx_metauniv(level const & l);
unsigned to_meta_idx(level const & l);

/** \brief Create a special metavariable that can be used as a placeholder in #match.

    \remark The index \c i is encoded in the hierarchical name, and can be quickly accessed.
    In the match procedure the substitution is also efficiently represented as an array (aka buffer).
*/
expr mk_idx_metavar(unsigned i, expr const & type);
/** \brief Return true iff \c l is a metavariable created using \c mk_idx_metavar */
bool is_idx_metavar(expr const & l);
unsigned to_meta_idx(expr const & e);

/** \brief Return true iff \c e contains idx metavariables or universe metavariables */
bool has_idx_metavar(expr const & e);
bool has_idx_expr_metavar(expr const & e);
bool has_idx_metauniv(level const & l);

class metavar_context;

/** \brief Convert metavariables occurring in \c e into indexed/temporary metavariables.
    New metavariables are added to new_us and new_ms. */
expr to_idx_metavars(metavar_context const & mctx, expr const & e, buffer<level> & new_us, buffer<expr> & new_ms);

void initialize_idx_metavar();
void finalize_idx_metavar();
}
