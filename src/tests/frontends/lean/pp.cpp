/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/abstract.h"
#include "kernel/kernel.h"
#include "library/printer.h"
#include "library/io_state_stream.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/pp.h"
#include "frontends/lua/register_modules.h"
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
    environment env; io_state ios = init_frontend(env);
    formatter fmt = mk_pp_formatter(env);
    std::cout << "Basic printer\n";
    std::cout << mk_shared_expr(10) << std::endl;
    std::cout << "----------------------------\nPretty printer\n";
    std::cout << fmt(mk_shared_expr(10)) << std::endl;
}

static void tst2() {
    environment env; io_state ios = init_frontend(env);
    formatter fmt = mk_pp_formatter(env);
    expr a = Const("a");
    expr t = Fun({a, Type()}, mk_shared_expr(10));
    expr g = Const("g");
    std::cout << fmt(g(t, t, t)) << std::endl;
    formatter fmt2 = mk_pp_formatter(env);
    std::cout << fmt2(g(t, t, t), options({"lean", "pp", "alias_min_weight"}, 100)) << std::endl;
}

static void tst3() {
    environment env; io_state ios = init_frontend(env);
    formatter fmt = mk_pp_formatter(env);
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
    environment env; io_state ios = init_frontend(env);
    io_state const & s1 = ios;
    io_state s2 = ios;
    regular(s1) << And(Const("a"), Const("b")) << "\n";
    regular(ios) << And(Const("a"), Const("b")) << "\n";
    diagnostic(ios) << And(Const("a"), Const("b")) << "\n";
    ios.set_option(name{"lean", "pp", "notation"}, false);
    regular(ios) << And(Const("a"), Const("b")) << "\n";
    regular(s1) << And(Const("a"), Const("b")) << "\n";
    regular(s2) << And(Const("a"), Const("b")) << "\n";
}

static void tst5() {
    environment env; io_state ios = init_frontend(env);
    std::shared_ptr<string_output_channel> out(std::make_shared<string_output_channel>());
    ios.set_regular_channel(out);
    ios.set_option(name{"pp", "unicode"}, true);
    ios.set_option(name{"lean", "pp", "notation"}, true);
    regular(ios) << And(Const("a"), Const("b"));
    lean_assert(out->str() == "a ∧ b");
    ios.set_option(name{"lean", "pp", "notation"}, false);
    regular(ios) << " " << And(Const("a"), Const("b"));
    lean_assert(out->str() == "a ∧ b and a b");
}

static expr mk_deep(unsigned depth) {
    if (depth == 0)
        return Const("a");
    else
        return Const("f")(mk_deep(depth - 1));
}

static void tst6() {
    environment env; io_state ios = init_frontend(env);
    std::shared_ptr<string_output_channel> out(std::make_shared<string_output_channel>());
    ios.set_regular_channel(out);
    expr t = mk_deep(10);
    ios.set_option(name{"lean", "pp", "max_depth"}, 5);
    ios.set_option(name{"pp", "colors"}, false);
    ios.set_option(name{"pp", "unicode"}, false);
    regular(ios) << t;
    lean_assert(out->str() == "f (f (f (f (f (...)))))");
}

int main() {
    save_stack_info();
    register_modules();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    return has_violations() ? 1 : 0;
}
