/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr_maps.h"

namespace lean {
/**
   \brief Base class for implementing operations that apply modifications
   on expressions.
   The default behavior is a NOOP, users must create subclasses and
   redefine the visit_* methods. */
class replace_visitor {
protected:
    typedef expr_bi_map<expr> cache;
    cache   m_cache;
    expr save_result(expr const & e, expr && r, bool shared);
    virtual expr visit_sort(expr const &);
    virtual expr visit_constant(expr const &);
    virtual expr visit_var(expr const &);
    virtual expr visit_meta(expr const &);
    virtual expr visit_fvar(expr const &);
    virtual expr visit_app(expr const &);
    virtual expr visit_binding(expr const &);
    virtual expr visit_lambda(expr const &);
    virtual expr visit_pi(expr const &);
    virtual expr visit_let(expr const & e);
    virtual expr visit_lit(expr const & e);
    virtual expr visit_mdata(expr const & e);
    virtual expr visit_proj(expr const & e);
    virtual expr visit(expr const &);
public:
    expr operator()(expr const & e) { return visit(e); }
    void clear() { m_cache.clear(); }
};
}
