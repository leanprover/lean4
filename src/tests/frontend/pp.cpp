/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontend.h"
#include "printer.h"
#include "abstract.h"
#include "builtin.h"
#include "pp.h"
#include "test.h"
using namespace lean;

static expr mk_shared_expr(unsigned depth) {
    expr f = Const("f");
    expr a = Const("a");
    expr r = a;
    for (unsigned i = 0; i < depth; i++)
        r = f(r, r);
    return r;
}

static void tst1() {
    frontend f;
    formatter fmt = mk_pp_formatter(f);
    std::cout << "Basic printer\n";
    std::cout << mk_shared_expr(10) << std::endl;
    std::cout << "----------------------------\nPretty printer\n";
    std::cout << fmt(mk_shared_expr(10)) << std::endl;
}

static void tst2() {
    frontend f;
    formatter fmt = mk_pp_formatter(f);
    expr a = Const("a");
    expr t = Fun({a, Type()}, mk_shared_expr(10));
    expr g = Const("g");
    std::cout << fmt(g(t, t, t)) << std::endl;
    formatter fmt2 = mk_pp_formatter(f);
    std::cout << fmt2(g(t, t, t), options({"pp", "alias_min_weight"}, 100)) << std::endl;
}

static void tst3() {
    frontend f;
    formatter fmt = mk_pp_formatter(f);
    expr g = Const("g");
    expr a = Const("\u03BA");
    expr b = Const("\u03C1");
    expr c = Const("\u03BD");
    expr d = Const(name("\u03BD", 1u));
    expr t = g(a, mk_shared_expr(5));
    std::cout << "----------------\n";
    std::cout << fmt(t) << "\n----------------\n";
    std::cout << fmt(g(b, t)) << "\n----------------\n";
    std::cout << fmt(g(c, b, t)) << "\n----------------\n";
    std::cout << fmt(g(d, c, b, t)) << "\n";
}

static void tst4() {
    frontend f;
    state const & s = f.get_state();
    regular(s) << And(Const("a"), Const("b")) << "\n";
    regular(f) << And(Const("a"), Const("b")) << "\n";
    diagnostic(f) << And(Const("a"), Const("b")) << "\n";
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    return has_violations() ? 1 : 0;
}
