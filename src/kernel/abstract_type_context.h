/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/** \brief This is a basic API for implementing macro definitions,
    kernel extensions, formatters, etc.

    \remark This class will eventually replace the class extension_context.

    \remark This class is already using the Lean 0.3 approach where
    constraint_seq is not used. */
class abstract_type_context {
public:
    virtual ~abstract_type_context() {}
    virtual environment const & env() const = 0;
    virtual expr whnf(expr const & e) = 0;
    virtual name next_name() = 0;
    virtual expr relaxed_whnf(expr const & e) { return whnf(e); }
    virtual bool is_def_eq(expr const & e1, expr const & e2) = 0;
    virtual bool relaxed_is_def_eq(expr const & e1, expr const & e2) { return is_def_eq(e1, e2); }
    virtual expr infer(expr const & e) = 0;
    /** \brief Simular to \c infer, but also performs type checking.
        \remark Default implementation just invokes \c infer. */
    virtual expr check(expr const & e) { return infer(e); }
    virtual optional<expr> is_stuck(expr const &) { return none_expr(); }

    virtual bool is_trusted_only() const { return false; }

    virtual expr push_local(name const & pp_name, expr const & type, binder_info const & bi = binder_info());
    virtual void pop_local();
    virtual bool has_local_pp_name(name const & pp_name);
    virtual expr abstract_locals(expr const & e, unsigned num_locals, expr const * locals);

    expr check(expr const & e, bool infer_only) { return infer_only ? infer(e) : check(e); }
};

class push_local_fn {
    abstract_type_context & m_ctx;
    unsigned                m_counter;
public:
    push_local_fn(abstract_type_context & ctx):m_ctx(ctx), m_counter(0) {}
    ~push_local_fn();
    expr operator()(name const & pp_name, expr const & type, binder_info const & bi = binder_info()) {
        m_counter++;
        return m_ctx.push_local(pp_name, type, bi);
    }
};
}
