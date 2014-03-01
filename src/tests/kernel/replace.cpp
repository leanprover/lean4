/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/name.h"
#include "kernel/expr.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/expr_maps.h"
#include "kernel/replace_fn.h"
using namespace lean;

expr mk_big(expr f, unsigned depth, unsigned val) {
    if (depth == 1)
        return mk_constant(name(name("foo"), val));
    else
        return f(mk_big(f, depth - 1, val << 1), mk_big(f, depth - 1, (val << 1) + 1));
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
    expr r = mk_lambda("x", Type, mk_app({Var(0), Var(1), Var(2)}));
    std::cout << instantiate_with_closed(r, Const("a")) << std::endl;
    lean_assert(instantiate_with_closed(r, Const("a")) == mk_lambda("x", Type, mk_app({Var(0), Const("a"), Var(1)})));
    lean_assert(instantiate_with_closed(instantiate_with_closed(r, Const("a")), Const("b")) ==
                mk_lambda("x", Type, mk_app({Var(0), Const("a"), Const("b")})));
    std::cout << instantiate_with_closed(binder_body(r), Const("a")) << std::endl;
    lean_assert(instantiate_with_closed(binder_body(r), Const("a")) == mk_app({Const("a"), Var(0), Var(1)}));
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

static expr arg(expr n, unsigned i) {
    buffer<expr> args;
    while (is_app(n)) {
        args.push_back(app_arg(n));
        n = app_fn(n);
    }
    args.push_back(n);
    return args[args.size() - i - 1];
}

static void tst3() {
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr c = Const("c");
    expr d = Const("d");
    expr A = Const("A");
    expr_map<expr> trace;
    auto proc = [&](expr const & x, unsigned offset) -> optional<expr> {
        if (is_var(x)) {
            unsigned vidx = var_idx(x);
            if (vidx == offset)
                return some_expr(c);
            else if (vidx > offset)
                return some_expr(mk_var(vidx-1));
            else
                return none_expr();
        } else {
            return none_expr();
        }
    };
    replace_fn replacer(proc, tracer(trace));
    expr t = Fun({{x, A}, {y, A}}, f(x, f(f(f(x, x), f(y, d)), f(d, d))));
    expr b = binder_body(t);
    expr r = replacer(b);
    std::cout << r << "\n";
    lean_assert(r == Fun({y, A}, f(c, f(f(f(c, c), f(y, d)), f(d, d)))));
    for (auto p : trace) {
        std::cout << p.first << " --> " << p.second << "\n";
    }
    lean_assert(trace[c] == Var(1));
    std::cout << arg(arg(binder_body(r), 2), 2) << "\n";
    lean_assert(arg(arg(binder_body(r), 2), 2) == f(d, d));
    lean_assert(trace.find(arg(arg(binder_body(r), 2), 2)) == trace.end());
    lean_assert(trace.find(binder_body(r)) != trace.end());
    lean_assert(trace.find(arg(binder_body(r), 2)) != trace.end());
    lean_assert(trace.find(arg(arg(binder_body(r), 2), 1)) != trace.end());
    lean_assert(trace.find(arg(arg(arg(binder_body(r), 2), 1), 1)) != trace.end());
    lean_assert(trace.find(arg(arg(arg(binder_body(r), 2), 1), 2)) == trace.end());
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    std::cout << "done" << "\n";
    return has_violations() ? 1 : 0;
}
