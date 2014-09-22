/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
class expr;
/** \brief Create an expression definitionally equal to \c e, but it must have type \c t. */
expr mk_typed_expr(expr const & t, expr const & e);
/** \brief Return true iff \c e was created using #mk_typed_expr */
bool is_typed_expr(expr const & e);
/** \brief Return the type of a typed expression

    \remark get_typed_expr_type(mk_typed_expr(t, e)) == t
*/
expr get_typed_expr_type(expr const & e);
/** \brief Return the expression/denotation of a typed expression

    \remark get_typed_expr_type(mk_typed_expr(t, e)) == e
*/
expr get_typed_expr_expr(expr const & e);

void initialize_typed_expr();
void finalize_typed_expr();
}
