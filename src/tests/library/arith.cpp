/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/thread.h"
#include "util/test.h"
#include "kernel/builtin.h"
#include "kernel/normalizer.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "library/arith/arith.h"
#include "frontends/lean/frontend.h"
using namespace lean;

static void tst0() {
    environment env;
    init_frontend(env);
    normalizer  norm(env);
    env->add_var("n", Nat);
    expr n = Const("n");
    lean_assert_eq(mk_nat_type(), Nat);
    lean_assert_eq(norm(nMul(nVal(2), nVal(3))), nVal(6));
    lean_assert_eq(norm(nLe(nVal(2), nVal(3))), True);
    lean_assert_eq(norm(nLe(nVal(5), nVal(3))), False);
    lean_assert_eq(norm(nLe(nVal(2), nVal(3))), True);
    lean_assert_eq(norm(nLe(n, nVal(3))), nLe(n, nVal(3)));
    env->add_var("x", Real);
    expr x = Const("x");
    lean_assert_eq(mk_real_type(), Real);
    lean_assert_eq(norm(rMul(rVal(2), rVal(3))), rVal(6));
    lean_assert_eq(norm(rDiv(rVal(2), rVal(0))), rVal(0));
    lean_assert_eq(norm(rLe(rVal(2),  rVal(3))), True);
    lean_assert_eq(norm(rLe(rVal(5),  rVal(3))), False);
    lean_assert_eq(norm(rLe(rVal(2),  rVal(3))), True);
    lean_assert_eq(norm(rLe(x, rVal(3))), rLe(x, rVal(3)));
    env->add_var("i", Int);
    expr i = Const("i");
    lean_assert_eq(norm(i2r(i)), i2r(i));
    lean_assert_eq(norm(i2r(iVal(2))), rVal(2));
    lean_assert_eq(mk_int_type(), Int);
    lean_assert_eq(norm(n2i(n)), n2i(n));
    lean_assert_eq(norm(n2i(nVal(2))), iVal(2));
    lean_assert_eq(norm(iDiv(iVal(2), iVal(0))), iVal(0));
}

static void tst1() {
    environment env;
    init_frontend(env);
    expr e = mk_int_value(mpz(10));
    lean_assert(is_int_value(e));
    lean_assert(type_check(e, env) == Int);
    std::cout << "e: " << e << "\n";
}

static void tst2() {
    environment env;
    init_frontend(env);
    expr e = iAdd(iVal(10), iVal(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == iVal(40));
    std::cout << type_check(mk_int_add_fn(), env) << "\n";
    lean_assert(type_check(e, env) == Int);
    lean_assert(type_check(mk_app(mk_int_add_fn(), iVal(10)), env) == (Int >> Int));
    lean_assert(is_int_value(normalize(e, env)));
    expr e2 = Fun("a", Int, iAdd(Const("a"), iAdd(iVal(10), iVal(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(type_check(e2, env) == mk_arrow(Int, Int));
    lean_assert(normalize(e2, env) == Fun("a", Int, iAdd(Const("a"), iVal(40))));
}

static void tst3() {
    environment env;
    init_frontend(env);
    expr e = iMul(iVal(10), iVal(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == iVal(300));
    std::cout << type_check(mk_int_mul_fn(), env) << "\n";
    lean_assert(type_check(e, env) == Int);
    lean_assert(type_check(mk_app(mk_int_mul_fn(), iVal(10)), env) == mk_arrow(Int, Int));
    lean_assert(is_int_value(normalize(e, env)));
    expr e2 = Fun("a", Int, iMul(Const("a"), iMul(iVal(10), iVal(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(type_check(e2, env) == (Int >> Int));
    lean_assert(normalize(e2, env) == Fun("a", Int, iMul(Const("a"), iVal(300))));
}

static void tst4() {
    environment env;
    init_frontend(env);
    expr e = iSub(iVal(10), iVal(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    lean_assert(normalize(e, env, context(), true) == iVal(-20));
    std::cout << type_check(mk_int_sub_fn(), env) << "\n";
    lean_assert(type_check(e, env) == Int);
    lean_assert(type_check(mk_app(mk_int_sub_fn(), iVal(10)), env) == mk_arrow(Int, Int));
    lean_assert(is_int_value(normalize(e, env, context(), true)));
    expr e2 = Fun("a", Int, iSub(Const("a"), iSub(iVal(10), iVal(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(type_check(e2, env) == (Int >> Int));
    lean_assert_eq(normalize(e2, env, context(), true), Fun("a", Int, iAdd(Const("a"), iVal(20))));
}

static void tst5() {
    environment env;
    init_frontend(env);
    env->add_var(name("a"), Int);
    expr e = Eq(iVal(3), iVal(4));
    std::cout << e << " --> " << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == False);
    lean_assert(normalize(Eq(Const("a"), iVal(3)), env) == Eq(Const("a"), iVal(3)));
}

static void tst6() {
    std::cout << "tst6\n";
    std::cout << mk_int_add_fn().raw() << "\n";
    std::cout << mk_int_add_fn().raw() << "\n";

    #ifndef __APPLE__
    thread t1([](){ save_stack_info(); std::cout << "t1: " << mk_int_add_fn().raw() << "\n"; });
    t1.join();
    thread t2([](){ save_stack_info(); std::cout << "t2: " << mk_int_add_fn().raw() << "\n"; });
    t2.join();
    #endif
    std::cout << mk_int_add_fn().raw() << "\n";
}

int main() {
    save_stack_info();
    tst0();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    return has_violations() ? 1 : 0;
}
