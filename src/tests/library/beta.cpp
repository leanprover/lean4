/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "test.h"
#include "beta.h"
#include "abstract.h"
#include "printer.h"
using namespace lean;

static void tst1() {
    expr f = Const("f");
    expr g = Const("g");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr A = Const("A");
    expr a = Const("a");
    expr b = Const("b");
    expr c = Const("c");
    expr d = Const("d");
    expr F = Fun({{x, A}, {y, A}, {z, A}}, f(x, g(y, x, z)));
    lean_assert(is_head_beta(F(a, b)));
    lean_assert(!is_head_beta(f(a,b)));
    lean_assert(!is_head_beta(Fun({x,A}, x)));
    std::cout << head_beta(F(a,b)) << "\n";
    lean_assert(head_beta(F(a,b)) == Fun({z, A}, f(a, g(b, a, z))));
    lean_assert(head_beta(F(a,b,c)) == f(a, g(b, a, c)));
    std::cout << head_beta(F(a,b,c,d)) << "\n";
    lean_assert(head_beta(F(a,b,c,d)) == mk_app(f(a, g(b, a, c)), d));
    lean_assert(head_beta(F(a)) == Fun({{y, A}, {z, A}}, f(a, g(y, a, z))));
    lean_assert(head_beta(F) == F);
    lean_assert(head_beta(f(a,b)) == f(a,b));
    lean_assert(head_beta(mk_app(Fun({x,A}, x), a, b)) == a(b));
    lean_assert(head_beta(mk_app(Fun({x,A}, x), a)) == a);
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}
