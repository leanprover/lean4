/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/extension_context.h"
#include "kernel/expr.h"

namespace lean {
expr extension_context::whnf(expr const & e, constraint_seq & cs) {
    auto p = whnf(e); cs += p.second; return p.first;
}
expr extension_context::check_type(expr const & e, constraint_seq & cs, bool infer_only) {
    auto p = check_type(e, infer_only); cs += p.second; return p.first;
}
pair<expr, constraint_seq> extension_context::infer(expr const & e) {
    bool infer_only = true;
    return check_type(e, infer_only);
}
expr extension_context::infer_type(expr const & e, constraint_seq & cs) {
    bool infer_only = true;
    auto p = check_type(e, infer_only); cs += p.second; return p.first;
}
bool extension_context::is_def_eq(expr const & e1, expr const & e2, delayed_justification & j, constraint_seq & cs) {
    auto p = is_def_eq(e1, e2, j); cs += p.second; return p.first;
}
}
