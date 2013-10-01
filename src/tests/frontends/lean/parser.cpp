/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "util/test.h"
#include "util/exception.h"
#include "util/numerics/mpq.h"
#include "kernel/builtin.h"
#include "kernel/printer.h"
#include "library/arith/arith.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/pp.h"
using namespace lean;

static void parse(frontend & fe, char const * str) {
    frontend child = fe.mk_child();
    std::istringstream in(str);
    if (parse_commands(child, in)) {
        formatter fmt = mk_pp_formatter(child);
        std::for_each(child.begin_local_objects(),
                      child.end_local_objects(),
                      [&](object const & obj) {
                          std::cout << fmt(obj) << "\n";
                          std::cout << obj << "\n";
                      });
    }
}

static void parse_error(frontend & fe, char const * str) {
    try {
        parse(fe, str);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
}

static void tst1() {
    frontend fe;
    parse(fe, "Variable x : Bool Variable y : Bool Axiom H : x && y || x => x");
    parse(fe, "Eval true && true");
    parse(fe, "Show true && false Eval true && false");
    parse(fe, "Infixl 35 & : and Show true & false & false Eval true & false");
    parse(fe, "Notation 100 if _ then _ fi : implies Show if true then false fi");
    parse(fe, "Show Pi (A : Type), A -> A");
    parse(fe, "Check Pi (A : Type), A -> A");
}

static void check(frontend const & fe, char const * str, expr const & expected) {
    std::istringstream in(str);
    try {
        expr got = parse_expr(fe, in);
        lean_assert(expected == got);
    } catch (exception &) {
        lean_unreachable();
    }
}

static void tst2() {
    frontend fe;
    fe.add_var("x", Bool);
    fe.add_var("y", Bool);
    fe.add_var("z", Bool);
    expr x = Const("x"); expr y = Const("y"); expr z = Const("z");
    check(fe, "x && y", And(x, y));
    check(fe, "x && y || z", Or(And(x, y), z));
    check(fe, "x || y && z", Or(x, And(y, z)));
    check(fe, "x || y || x && z", Or(x, Or(y, And(x, z))));
    check(fe, "x || y || x && z => x && y", Implies(Or(x, Or(y, And(x, z))), And(x, y)));
    check(fe, "x ∨ y ∨ x ∧ z ⇒ x ∧ y", Implies(Or(x, Or(y, And(x, z))), And(x, y)));
    check(fe, "x⇒y⇒z⇒x", Implies(x, Implies(y, Implies(z, x))));
    check(fe, "x=>y=>z=>x", Implies(x, Implies(y, Implies(z, x))));
    check(fe, "x=>(y=>z)=>x", Implies(x, Implies(Implies(y, z), x)));
}

static void tst3() {
    frontend fe;
    parse(fe, "Help");
    parse(fe, "Help Options");
    parse_error(fe, "Help Echo");
    check(fe, "10.3", mk_real_value(mpq(103, 10)));
    parse(fe, "Variable f : Real -> Real. Check f 10.3.");
    parse(fe, "Variable g : Type 1 -> Type. Check g Type");
    parse_error(fe, "Check fun .");
    parse_error(fe, "Definition foo .");
    parse_error(fe, "Check a");
    parse_error(fe, "Check U");
    parse(fe, "Variable h : Real -> Real -> Real. Notation 10 [ _ ; _ ] : h. Check [ 10.3 ; 20.1 ].");
    parse_error(fe, "Variable h : Real -> Real -> Real. Notation 10 [ _ ; _ ] : h. Check [ 10.3 | 20.1 ].");
    parse_error(fe, "Set pp::indent true");
    parse(fe, "Set pp::indent 10");
    parse_error(fe, "Set pp::colors foo");
    parse_error(fe, "Set pp::colors \"foo\"");
    parse(fe, "Set pp::colors true");
    parse_error(fe, "Notation 10 : Int::add");
    parse_error(fe, "Notation 10 _ : Int::add");
    parse(fe, "Notation 10 _ ++ _ : Int::add. Eval 10 ++ 20.");
    parse(fe, "Notation 10 _ -- : Int::neg. Eval 10 --");
    parse(fe, "Notation 30 -- _ : Int::neg. Eval -- 10");
    parse_error(fe, "10 + 30");
}

int main() {
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}
