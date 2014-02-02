/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/thread.h"
#include "util/test.h"
#include "kernel/kernel.h"
#include "kernel/normalizer.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "library/io_state_stream.h"
#include "library/arith/arith.h"
#include "frontends/lean/frontend.h"
#include "frontends/lua/register_modules.h"
using namespace lean;

static void tst0() {
    environment env;
    init_test_frontend(env);
    normalizer  norm(env);
    env->add_var("n", Nat);
    expr n = Const("n");
    lean_assert_eq(mk_nat_type(), Nat);
    env->add_var("x", Real);
    expr x = Const("x");
    lean_assert_eq(mk_real_type(), Real);
    env->add_var("i", Int);
    expr i = Const("i");
    lean_assert_eq(mk_int_type(), Int);
}

static void tst1() {
    environment env;
    init_test_frontend(env);
    expr e = mk_int_value(mpz(10));
    lean_assert(is_int_value(e));
    lean_assert(type_check(e, env) == Int);
    std::cout << "e: " << e << "\n";
}

static void tst2() {
    environment env;
    init_test_frontend(env);
    expr e = mk_Int_add(iVal(10), iVal(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    std::cout << type_check(mk_Int_add_fn(), env) << "\n";
    lean_assert(type_check(e, env) == Int);
    lean_assert(type_check(mk_app(mk_Int_add_fn(), iVal(10)), env) == (Int >> Int));
    expr e2 = Fun("a", Int, mk_Int_add(Const("a"), mk_Int_add(iVal(10), iVal(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(type_check(e2, env) == mk_arrow(Int, Int));
}

static void tst3() {
    environment env;
    init_test_frontend(env);
    expr e = mk_Int_mul(iVal(10), iVal(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    std::cout << type_check(mk_Int_mul_fn(), env) << "\n";
    lean_assert(type_check(e, env) == Int);
    lean_assert(type_check(mk_app(mk_Int_mul_fn(), iVal(10)), env) == mk_arrow(Int, Int));
    expr e2 = Fun("a", Int, mk_Int_mul(Const("a"), mk_Int_mul(iVal(10), iVal(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(type_check(e2, env) == (Int >> Int));
}

static void tst4() {
    environment env;
    init_test_frontend(env);
    expr e = mk_Int_sub(iVal(10), iVal(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    std::cout << type_check(mk_Int_sub_fn(), env) << "\n";
    lean_assert(type_check(e, env) == Int);
    lean_assert(type_check(mk_app(mk_Int_sub_fn(), iVal(10)), env) == mk_arrow(Int, Int));
    expr e2 = Fun("a", Int, mk_Int_sub(Const("a"), mk_Int_sub(iVal(10), iVal(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(type_check(e2, env) == (Int >> Int));
}

static void tst5() {
    environment env;
    init_test_frontend(env);
    env->add_var(name("a"), Int);
    expr e = mk_eq(Int, iVal(3), iVal(4));
    std::cout << e << " --> " << normalize(e, env) << "\n";
}

static void tst6() {
    std::cout << "tst6\n";
    std::cout << mk_Int_add_fn().raw() << "\n";
    std::cout << mk_Int_add_fn().raw() << "\n";

    #ifndef __APPLE__
    thread t1([](){ save_stack_info(); std::cout << "t1: " << mk_Int_add_fn().raw() << "\n"; });
    t1.join();
    thread t2([](){ save_stack_info(); std::cout << "t2: " << mk_Int_add_fn().raw() << "\n"; });
    t2.join();
    #endif
    std::cout << mk_Int_add_fn().raw() << "\n";
}

int main() {
    save_stack_info();
    register_modules();
    tst0();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    return has_violations() ? 1 : 0;
}
