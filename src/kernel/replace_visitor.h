/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr_maps.h"
#include "kernel/replace_fn.h"
#include "kernel/context.h"

namespace lean {
/**
   \brief Base class for implementing operations that apply modifications
   an expressions.
   The default behavior is a NOOP, users must create subclasses and
   redefine the visit_* methods.

   This is a more expensive (and flexible) version of replace_fn in
   the file kernel/replace.h
*/
class replace_visitor {
protected:
    typedef expr_map<expr> cache;
    cache   m_cache;
    context m_ctx;
    expr save_result(expr const & e, expr && r, bool shared);
    virtual expr visit_type(expr const &, context const &);
    virtual expr visit_value(expr const &, context const &);
    virtual expr visit_constant(expr const &, context const &);
    virtual expr visit_var(expr const &, context const &);
    virtual expr visit_metavar(expr const &, context const &);
    virtual expr visit_app(expr const &, context const &);
    virtual expr visit_eq(expr const &, context const &);
    virtual expr visit_abst(expr const &, context const &);
    virtual expr visit_lambda(expr const &, context const &);
    virtual expr visit_pi(expr const &, context const &);
    virtual expr visit_let(expr const &, context const &);
    virtual expr visit(expr const &, context const &);
    optional<expr> visit(optional<expr> const &, context const &);

    void set_ctx(context const & ctx) {
        if (!is_eqp(m_ctx, ctx)) {
            m_ctx = ctx;
            m_cache.clear();
        }
    }

public:
    expr operator()(expr const & e, context const & ctx = context()) {
        set_ctx(ctx);
        return visit(e, ctx);
    }

    void clear() {
        m_ctx = context();
        m_cache.clear();
    }
};
}
