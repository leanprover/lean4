/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr_sets.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/type_context.h"

namespace lean {
struct check_fn {
    type_context_old &   m_ctx;
    expr_set             m_visited;
public:
    check_fn(type_context_old & ctx):m_ctx(ctx) {}
};

void check(type_context_old &, expr const &) {
    lean_unreachable();
}

void initialize_check() {
    register_trace_class("check");
}

void finalize_check() {
}
}
