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
#include "kernel/builtin.h"
#include "kernel/printer.h"
#include "library/arith/arith.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/pp.h"
using namespace lean;

static void parse(environment const & env, io_state const & ios, char const * str) {
    environment child = env->mk_child();
    io_state ios_copy = ios;
    std::istringstream in(str);
    if (parse_commands(child, ios_copy, in)) {
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
    environment env; io_state ios; init_full_frontend(env, ios);
    parse(env, ios, "Variable x : Bool Variable y : Bool Axiom H : x && y || x => x");
    parse(env, ios, "Eval true && true");
    parse(env, ios, "Show true && false Eval true && false");
    parse(env, ios, "Infixl 35 & : and Show true & false & false Eval true & false");
    parse(env, ios, "Notation 100 if _ then _ fi : implies Show if true then false fi");
    parse(env, ios, "Show Pi (A : Type), A -> A");
    parse(env, ios, "Check Pi (A : Type), A -> A");
}

static void check(environment const & env, io_state & ios, char const * str, expr const & expected) {
    std::istringstream in(str);
    try {
        expr got = parse_expr(env, ios, in);
        lean_assert(expected == got);
    } catch (exception &) {
        lean_unreachable();
    }
}

static void tst2() {
    environment env; io_state ios; init_full_frontend(env, ios);
    env->add_var("x", Bool);
    env->add_var("y", Bool);
    env->add_var("z", Bool);
    expr x = Const("x"); expr y = Const("y"); expr z = Const("z");
    check(env, ios, "x && y", And(x, y));
    check(env, ios, "x && y || z", Or(And(x, y), z));
    check(env, ios, "x || y && z", Or(x, And(y, z)));
    check(env, ios, "x || y || x && z", Or(x, Or(y, And(x, z))));
    check(env, ios, "x || y || x && z => x && y", Implies(Or(x, Or(y, And(x, z))), And(x, y)));
    check(env, ios, "x ∨ y ∨ x ∧ z ⇒ x ∧ y", Implies(Or(x, Or(y, And(x, z))), And(x, y)));
    check(env, ios, "x⇒y⇒z⇒x", Implies(x, Implies(y, Implies(z, x))));
    check(env, ios, "x=>y=>z=>x", Implies(x, Implies(y, Implies(z, x))));
    check(env, ios, "x=>(y=>z)=>x", Implies(x, Implies(Implies(y, z), x)));
}

static void tst3() {
    environment env; io_state ios; init_full_frontend(env, ios);
    parse(env, ios, "Help");
    parse(env, ios, "Help Options");
    parse_error(env, ios, "Help Echo");
    check(env, ios, "10.3", mk_real_value(mpq(103, 10)));
    parse(env, ios, "Variable f : Real -> Real. Check f 10.3.");
    parse(env, ios, "Variable g : (Type 1) -> Type. Check g Type");
    parse_error(env, ios, "Check fun .");
    parse_error(env, ios, "Definition foo .");
    parse_error(env, ios, "Check a");
    parse_error(env, ios, "Check U");
    parse(env, ios, "Variable h : Real -> Real -> Real. Notation 10 [ _ ; _ ] : h. Check [ 10.3 ; 20.1 ].");
    parse_error(env, ios, "Variable h : Real -> Real -> Real. Notation 10 [ _ ; _ ] : h. Check [ 10.3 | 20.1 ].");
    parse_error(env, ios, "SetOption pp::indent true");
    parse(env, ios, "SetOption pp::indent 10");
    parse_error(env, ios, "SetOption pp::colors foo");
    parse_error(env, ios, "SetOption pp::colors \"foo\"");
    parse(env, ios, "SetOption pp::colors true");
    parse_error(env, ios, "Notation 10 : Int::add");
    parse_error(env, ios, "Notation 10 _ : Int::add");
    parse(env, ios, "Notation 10 _ ++ _ : Int::add. Eval 10 ++ 20.");
    parse(env, ios, "Notation 10 _ -- : Int::neg. Eval 10 --");
    parse(env, ios, "Notation 30 -- _ : Int::neg. Eval -- 10");
    parse_error(env, ios, "10 + 30");
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}
