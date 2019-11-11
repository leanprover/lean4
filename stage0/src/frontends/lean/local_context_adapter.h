/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/local_context.h"
#include "frontends/lean/local_decls.h"
namespace lean {
typedef local_decls<expr> local_expr_decls;
/** \brief Temporary helper class that allows us to convert local_expr_decls into local_context,
    and translate expressions back and forth the two representations.

    This helper class is needed because the old elaborator is based on the local_expr_decls
    structure, and the new one on the more efficient local_context.

    After the old elaborator is removed from the code base, we will be able to replace
    local_expr_decls with local_context in the parser, and avoid this adapter. */
class local_context_adapter {
    local_context m_lctx;
    buffer<expr>  m_locals;
    buffer<expr>  m_local_refs;
    /* Return true iff \c e has a local_decl reference */
    static bool has_local_ref(expr const & e);

    /* Return true iff \c e has a local constant that is not a local_decl reference */
    static bool has_regular_local(expr const & e);

    void add_local(expr const & local);
public:
    local_context_adapter(local_expr_decls const & ldecls);
    local_context_adapter(list<expr> const & lctx);
    expr translate_to(expr const & e) const;
    expr translate_from(expr const & e) const;
    local_context const & lctx() const { return m_lctx; }
};
}
