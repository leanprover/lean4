/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/** \brief Abstract context-like object */
class context {
public:
    virtual ~context() {}
    virtual expr get_type(name const & n) const = 0;
    virtual optional<expr> get_value(name const & n) const = 0;
};

/** \brief Create a reference to an object defined in a context.
    This is an auxiliary expression only used during elaboration (e.g., tactics and blast).
    The type (and optionally value) must be stored in a context-like object (see #context).
 */
expr mk_ref(name const & n);
/** \brief Return true iff \c e is an expression created using #mk_ref */
bool is_ref(expr const & e);
/** \brief Return the name of an expression created using #mk_ref */
name get_ref_name(expr const & e);

/** \brief Set the current context like object. It is setting thread local storage. */
class scope_context {
    context * m_old_context;
public:
    scope_context(context & ctx);
    ~scope_context();
};

void initialize_context();
void finalize_context();
}
