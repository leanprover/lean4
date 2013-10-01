/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/timeit.h"
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "kernel/printer.h"
#include "library/light_checker.h"
#include "library/arith/arith.h"
#include "library/all/all.h"
using namespace lean;

static void tst1() {
    environment env = mk_toplevel();
    light_checker type_of(env);
    expr f = Const("f");
    expr g = Const("g");
    expr a = Const("a");
    expr b = Const("b");
    expr A = Const("A");
    env.add_var("f", Int >> (Int >> Int));
    lean_assert(type_of(f(a, a)) == Int);
    lean_assert(type_of(f(a)) == Int >> Int);
    lean_assert(type_of(And(a, f(a))) == Bool);
    lean_assert(type_of(Fun({a, Int}, iAdd(a, iVal(1)))) == Int >> Int);
    lean_assert(type_of(Let({a, iVal(10)}, iAdd(a, b))) == Int);
    lean_assert(type_of(Type()) == Type(level() + 1));
    lean_assert(type_of(Bool) == Type());
    lean_assert(type_of(Pi({a, Type()}, Type(level() + 2))) == Type(level() + 3));
    lean_assert(type_of(Pi({a, Type(level()+4)}, Type(level() + 2))) == Type(level() + 5));
    lean_assert(type_of(Pi({a, Int}, Bool)) == Type());
    env.add_var("g", Pi({A, Type()}, A >> A));
    lean_assert(type_of(g(Int, a)) == Int);
    lean_assert(type_of(g(Fun({a, Type()}, a)(Int), a)) == Fun({a, Type()}, a)(Int));
}

static expr mk_big(unsigned val, unsigned depth) {
    if (depth == 0)
        return iVal(val);
    else
        return iAdd(mk_big(val*2, depth-1), mk_big(val*2 + 1, depth-1));
}

static void tst2() {
    environment env = mk_toplevel();
    light_checker type_of(env);
    type_checker  type_of_slow(env);
    expr t = mk_big(0, 10);
    {
        timeit timer(std::cout, "light checker 10000 calls");
        for (unsigned i = 0; i < 10000; i++) {
            type_of(t);
            type_of.clear();
        }
    }
    {
        timeit timer(std::cout, "type checker 300 calls");
        for (unsigned i = 0; i < 300; i++) {
            type_of_slow.infer_type(t);
            type_of_slow.clear();
        }
    }
}

static void tst3() {
    environment env;
    import_all(env);
    context ctx1, ctx2;
    expr A = Const("A");
    expr vec1 = Const("vec1");
    expr vec2 = Const("vec2");
    env.add_var("vec1", Int  >> (Type() >> Type()));
    env.add_var("vec2", Real >> (Type() >> Type()));
    ctx1 = extend(ctx1, "x", Int,  iVal(1));
    ctx1 = extend(ctx1, "f", Pi({A, Int}, vec1(A, Int)));
    ctx2 = extend(ctx2, "x", Real, rVal(2));
    ctx2 = extend(ctx2, "f", Pi({A, Real}, vec2(A, Real)));
    expr F = Var(0)(Var(1));
    expr F_copy = F;
    light_checker infer(env);
    std::cout << infer(F, ctx1) << "\n";
    lean_assert_eq(infer(F, ctx1), vec1(Var(1), Int));
    lean_assert_eq(infer(F, ctx2), vec2(Var(1), Real));
    lean_assert(is_eqp(infer(F, ctx2), infer(F, ctx2)));
    lean_assert(is_eqp(infer(F, ctx1), infer(F, ctx1)));
    expr r = infer(F, ctx1);
    infer.clear();
    lean_assert(!is_eqp(r, infer(F, ctx1)));
    r = infer(F, ctx1);
    lean_assert(is_eqp(r, infer(F, ctx1)));
}


int main() {
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}
