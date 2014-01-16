/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <sstream>
#include "util/test.h"
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "kernel/formatter.h"
#include "kernel/kernel.h"
#include "library/printer.h"
using namespace lean;

static void check(format const & f, char const * expected) {
    std::ostringstream strm;
    strm << f;
    std::cout << strm.str() << "\n";
    lean_assert_eq(strm.str(), expected);
}

static void tst1() {
    environment env;
    env->add_var("N", Type());
    formatter fmt = mk_simple_formatter();
    check(fmt(env), "variable N : Type\n");
    expr f  = Const("f");
    expr a  = Const("a");
    expr x  = Const("x");
    expr y  = Const("y");
    expr N  = Const("N");
    check(fmt(env->get_object("N")), "variable N : Type");
    context ctx;
    ctx = extend(ctx, "x", f(a));
    ctx = extend(ctx, "y", f(Var(0), N >> N));
    check(fmt(ctx, f(Var(0), Var(2))), "f y#0 #2");
    check(fmt(ctx, f(Var(0), Var(2)), true), "[x : f a; y : f x#0 (N -> N)] |- f y#0 #2");
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}
