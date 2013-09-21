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
#include "library/formatter.h"
using namespace lean;

static void check(format const & f, char const * expected) {
    std::ostringstream strm;
    strm << f;
    std::cout << strm.str() << "\n";
    lean_assert(strm.str() == expected);
}

static void tst1() {
    environment env;
    env.add_var("N", Type());
    formatter fmt = mk_simple_formatter();
    check(fmt(env), "Variable N : Type\n");
    expr f  = Const("f");
    expr a  = Const("a");
    expr x  = Const("x");
    expr y  = Const("y");
    expr N  = Const("N");
    expr F  = Fun({x, Pi({x, N}, x >> x)}, Let({y, f(a)}, f(Eq(x, f(y, a)))));
    check(fmt(F), "fun x : (Pi x : N, (x -> x)), (let y := f a in (f (x = (f y a))))");
    check(fmt(env.get_object("N")), "Variable N : Type");
    context ctx;
    ctx = extend(ctx, "x", f(a));
    ctx = extend(ctx, "y", f(Var(0), N >> N));
    ctx = extend(ctx, "z", N, Eq(Var(0), Var(1)));
    check(fmt(ctx), "[x : f a; y : f x (N -> N); z : N := y = x]");
    check(fmt(ctx, f(Var(0), Var(2))), "f z x");
    check(fmt(ctx, f(Var(0), Var(2)), true), "[x : f a; y : f x (N -> N); z : N := y = x] |- f z x");
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}
