/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class abstract_type_context {
    options m_options;
public:
    abstract_type_context(options const & opts):m_options(opts) {}
    abstract_type_context() {}
    options const & get_options() const { return m_options; }
    virtual ~abstract_type_context() {}
    virtual environment const & env() const { lean_unreachable(); }
    virtual expr whnf(expr const &) { lean_unreachable(); }
    virtual name next_name() { lean_unreachable(); }
    virtual expr relaxed_whnf(expr const &) { lean_unreachable(); }
    virtual bool is_def_eq(expr const &, expr const &) { lean_unreachable(); }
    virtual bool relaxed_is_def_eq(expr const &, expr const &) { lean_unreachable(); }
    virtual expr infer(expr const &) { lean_unreachable(); }
    /** \brief Simular to \c infer, but also performs type checking.
        \remark Default implementation just invokes \c infer. */
    virtual expr check(expr const &) { lean_unreachable(); }
    virtual optional<expr> is_stuck(expr const &) { lean_unreachable(); }
    virtual optional<name> get_local_pp_name(expr const &) { lean_unreachable(); }
    virtual expr push_local(name const &, expr const &, binder_info) { lean_unreachable(); }
    virtual void pop_local() { lean_unreachable(); }

    expr check(expr const &, bool) { lean_unreachable(); }
};

class push_local_fn {
    abstract_type_context & m_ctx;
    unsigned                m_counter;
public:
    push_local_fn(abstract_type_context & ctx):m_ctx(ctx), m_counter(0) {}
    ~push_local_fn();
    expr operator()(name const & pp_name, expr const & type, binder_info bi = mk_binder_info()) {
        m_counter++;
        return m_ctx.push_local(pp_name, type, bi);
    }
};
}
