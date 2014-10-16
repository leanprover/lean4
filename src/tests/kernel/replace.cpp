/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/name.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/expr.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/expr_maps.h"
#include "kernel/replace_fn.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/print.h"
using namespace lean;

expr mk_big(expr f, unsigned depth, unsigned val) {
    if (depth == 1)
        return mk_constant(name(name("foo"), val));
    else
        return mk_app(f, mk_big(f, depth - 1, val << 1), mk_big(f, depth - 1, (val << 1) + 1));
}

static void tst1() {
    expr f = Const("f");
    expr r = mk_big(f, 16, 0);
    expr n = Const(name("foo"));
    for (unsigned i = 0; i < 20; i++) {
        r = abstract(r, n);
    }
}

static void tst2() {
    expr Type = mk_Type();
    expr r = mk_lambda("x", Type, mk_app({Var(0), Var(1), Var(2)}));
    std::cout << instantiate(r, Const("a")) << std::endl;
    lean_assert(instantiate(r, Const("a")) == mk_lambda("x", Type, mk_app({Var(0), Const("a"), Var(1)})));
    lean_assert(instantiate(instantiate(r, Const("a")), Const("b")) ==
                mk_lambda("x", Type, mk_app({Var(0), Const("a"), Const("b")})));
    std::cout << instantiate(binding_body(r), Const("a")) << std::endl;
    lean_assert(instantiate(binding_body(r), Const("a")) == mk_app({Const("a"), Var(0), Var(1)}));
    std::cout << instantiate(r, Var(10)) << std::endl;
    lean_assert(instantiate(r, Var(10)) == mk_lambda("x", Type, mk_app({Var(0), Var(11), Var(1)})));
    std::cout << mk_pi("_", Var(3), Var(4)) << std::endl;
    std::cout << instantiate(mk_pi("_", Var(3), Var(4)), Var(0)) << std::endl;
    lean_assert(instantiate(mk_pi("_", Var(3), Var(4)), Var(0)) == mk_pi("_", Var(2), Var(3)));
}

class tracer {
    expr_map<expr> & m_trace;
public:
    tracer(expr_map<expr> & trace):m_trace(trace) {}

    void operator()(expr const & old_e, expr const & new_e) {
        if (!is_eqp(new_e, old_e)) {
            m_trace[new_e] = old_e;
        }
    }
};

int main() {
    save_stack_info();
    init_default_print_fn();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    tst1();
    tst2();
    std::cout << "done" << "\n";
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
