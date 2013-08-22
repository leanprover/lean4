/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "printer.h"
#include "abstract.h"
#include "builtin.h"
#include "lean_frontend.h"
#include "lean_pp.h"
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
    std::cout << fmt2(g(t, t, t), options({"lean", "pp", "alias_min_weight"}, 100)) << std::endl;
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
    state const & s1 = f.get_state();
    state s2 = f.get_state();
    regular(s1) << And(Const("a"), Const("b")) << "\n";
    regular(f) << And(Const("a"), Const("b")) << "\n";
    diagnostic(f) << And(Const("a"), Const("b")) << "\n";
    f.set_option(name{"lean", "pp", "notation"}, false);
    regular(f) << And(Const("a"), Const("b")) << "\n";
    regular(s1) << And(Const("a"), Const("b")) << "\n";
    regular(s2) << And(Const("a"), Const("b")) << "\n";
}

static void tst5() {
    frontend f;
    std::shared_ptr<string_output_channel> out(new string_output_channel());
    f.set_regular_channel(out);
    regular(f) << And(Const("a"), Const("b"));
    lean_assert(out->str() == "a ∧ b");
    f.set_option(name{"lean", "pp", "notation"}, false);
    regular(f) << " " << And(Const("a"), Const("b"));
    lean_assert(out->str() == "a ∧ b and a b");
}

static expr mk_deep(unsigned depth) {
    if (depth == 0)
        return Const("a");
    else
        return Const("f")(mk_deep(depth - 1));
}

static void tst6() {
    frontend f;
    std::shared_ptr<string_output_channel> out(new string_output_channel());
    f.set_regular_channel(out);
    expr t = mk_deep(10);
    f.set_option(name{"lean", "pp", "max_depth"}, 5);
    f.set_option(name{"pp", "colors"}, false);
    regular(f) << t;
    lean_assert(out->str() == "f (f (f (f (f (…)))))");
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    return has_violations() ? 1 : 0;
}
