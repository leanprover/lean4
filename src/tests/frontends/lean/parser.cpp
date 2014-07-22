/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <memory>
#include "util/test.h"
#include "util/exception.h"
#include "util/numerics/mpq.h"
#include "kernel/kernel.h"
#include "library/printer.h"
#include "library/io_state_stream.h"
#include "library/arith/arith.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/pp.h"
#include "frontends/lua/register_modules.h"
using namespace lean;

static void parse(environment const & env, io_state const & ios, char const * str) {
    environment child = env->mk_child();
    io_state ios_copy = ios;
    std::istringstream in(str);
    if (parse_commands(child, ios_copy, in, "[string]")) {
        formatter fmt = mk_pp_formatter(env);
        std::for_each(child->begin_local_objects(),
                      child->end_local_objects(),
                      [&](object const & obj) {
                          std::cout << fmt(obj) << "\n";
                          std::cout << obj << "\n";
                      });
    }
}

static void parse_error(environment const & env, io_state const & ios, char const * str) {
    try {
        parse(env, ios, str);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
}

static void tst1() {
    environment env; io_state ios = init_test_frontend(env);
    parse(env, ios, "variable x : Prop variable y : Prop axiom H : x && y || x -> x");
    parse(env, ios, "eval true && true");
    parse(env, ios, "print true && false eval true && false");
    parse(env, ios, "infixl 35 & : and print true & false & false eval true & false");
    parse(env, ios, "notation 100 if _ then _ fi : implies print if true then false fi");
    parse(env, ios, "print forall (A : Type), A -> A");
    parse(env, ios, "check forall (A : Type), A -> A");
}

static void check(environment const & env, io_state & ios, char const * str, expr const & expected) {
    std::istringstream in(str);
    try {
        expr got = parse_expr(env, ios, in, "[string]");
        lean_assert(expected == got);
    } catch (exception &) {
        lean_unreachable();
    }
}

static void tst2() {
    environment env; io_state ios = init_test_frontend(env);
    env->add_var("x", Prop);
    env->add_var("y", Prop);
    env->add_var("z", Prop);
    expr x = Const("x"); expr y = Const("y"); expr z = Const("z");
    check(env, ios, "x && y", And(x, y));
    check(env, ios, "x && y || z", Or(And(x, y), z));
    check(env, ios, "x || y && z", Or(x, And(y, z)));
    check(env, ios, "x || y || x && z", Or(x, Or(y, And(x, z))));
    check(env, ios, "x || y || x && z -> x && y", mk_arrow(Or(x, Or(y, And(x, z))), And(x, y)));
    check(env, ios, "x ∨ y ∨ x ∧ z → x ∧ y", mk_arrow(Or(x, Or(y, And(x, z))), And(x, y)));
    check(env, ios, "x→y→z→x", mk_arrow(x, mk_arrow(y, mk_arrow(z, x))));
    check(env, ios, "x->y->z->x", mk_arrow(x, mk_arrow(y, mk_arrow(z, x))));
    check(env, ios, "x->(y->z)->x", mk_arrow(x, mk_arrow(mk_arrow(y, z), x)));
}

static void tst3() {
    environment env; io_state ios = init_test_frontend(env);
    parse(env, ios, "help");
    parse(env, ios, "help options");
    parse_error(env, ios, "help print");
    check(env, ios, "10.3", mk_real_value(mpq(103, 10)));
    parse(env, ios, "variable f : Real -> Real. check f 10.3.");
    parse(env, ios, "variable g : (Type 1) -> Type. check g Type");
    parse_error(env, ios, "check fun .");
    parse_error(env, ios, "definition foo .");
    parse_error(env, ios, "check a");
    parse_error(env, ios, "check U");
    parse(env, ios, "variable h : Real -> Real -> Real. notation 10 [ _ ; _ ] : h. check [ 10.3 ; 20.1 ].");
    parse_error(env, ios, "variable h : Real -> Real -> Real. notation 10 [ _ ; _ ] : h. check [ 10.3 | 20.1 ].");
    parse_error(env, ios, "set_option pp::indent true");
    parse(env, ios, "set_option pp::indent 10");
    parse_error(env, ios, "set_option pp::colors foo");
    parse_error(env, ios, "set_option pp::colors \"foo\"");
    parse(env, ios, "set_option pp::colors true");
    parse_error(env, ios, "notation 10 : Int::add");
    parse_error(env, ios, "notation 10 _ : Int::add");
    parse(env, ios, "notation 10 _ ++ _ : Int::add. eval 10 ++ 20.");
    parse(env, ios, "notation 10 _ -+ : Int::neg. eval 10 -+");
    parse(env, ios, "notation 30 -+ _ : Int::neg. eval -+ 10");
    parse_error(env, ios, "10 + 30");
}

int main() {
    save_stack_info();
    register_modules();
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}
