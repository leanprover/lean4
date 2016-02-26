/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/fresh_name.h"
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
    virtual expr relaxed_whnf(expr const & e) { return whnf(e); }
    virtual bool is_def_eq(expr const & e1, expr const & e2) = 0;
    virtual bool relaxed_is_def_eq(expr const & e1, expr const & e2) { return is_def_eq(e1, e2); }
    virtual expr infer(expr const & e) = 0;
    /** \brief Simular to \c infer, but also performs type checking.
        \remark Default implementation just invokes \c infer. */
    virtual expr check(expr const & e) { return infer(e); }
    virtual optional<expr> is_stuck(expr const &) { return none_expr(); }
    virtual name get_local_pp_name(expr const & e) const { return local_pp_name(e); }
    virtual expr mk_tmp_local(name const & pp_name, expr const & type, binder_info const & bi = binder_info()) {
        return mk_local(mk_fresh_name(), pp_name, type, bi);
    }
};
}
