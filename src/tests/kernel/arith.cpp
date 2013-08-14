/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <thread>
#include "environment.h"
#include "type_check.h"
#include "builtin.h"
#include "arith.h"
#include "normalize.h"
#include "abstract.h"
#include "test.h"
using namespace lean;

static void tst1() {
    environment env;
    expr e = mk_int_value(mpz(10));
    lean_assert(is_int_value(e));
    lean_assert(infer_type(e, env) == Int);
    std::cout << "e: " << e << "\n";
}

static void tst2() {
    environment env;
    expr e = iAdd(iVal(10), iVal(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == iVal(40));
    std::cout << infer_type(mk_int_add_fn(), env) << "\n";
    lean_assert(infer_type(e, env) == Int);
    lean_assert(infer_type(mk_app(mk_int_add_fn(), iVal(10)), env) == (Int >> Int));
    lean_assert(is_int_value(normalize(e, env)));
    expr e2 = Fun("a", Int, iAdd(Const("a"), iAdd(iVal(10), iVal(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(infer_type(e2, env) == arrow(Int, Int));
    lean_assert(normalize(e2, env) == Fun("a", Int, iAdd(Const("a"), iVal(40))));
}

static void tst3() {
    environment env;
    expr e = iMul(iVal(10), iVal(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == iVal(300));
    std::cout << infer_type(mk_int_mul_fn(), env) << "\n";
    lean_assert(infer_type(e, env) == Int);
    lean_assert(infer_type(mk_app(mk_int_mul_fn(), iVal(10)), env) == arrow(Int, Int));
    lean_assert(is_int_value(normalize(e, env)));
    expr e2 = Fun("a", Int, iMul(Const("a"), iMul(iVal(10), iVal(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(infer_type(e2, env) == (Int >> Int));
    lean_assert(normalize(e2, env) == Fun("a", Int, iMul(Const("a"), iVal(300))));
}

static void tst4() {
    environment env;
    expr e = iSub(iVal(10), iVal(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == iVal(-20));
    std::cout << infer_type(mk_int_sub_fn(), env) << "\n";
    lean_assert(infer_type(e, env) == Int);
    lean_assert(infer_type(mk_app(mk_int_sub_fn(), iVal(10)), env) == arrow(Int, Int));
    lean_assert(is_int_value(normalize(e, env)));
    expr e2 = Fun("a", Int, iSub(Const("a"), iSub(iVal(10), iVal(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(infer_type(e2, env) == (Int >> Int));
    lean_assert(normalize(e2, env) == Fun("a", Int, iSub(Const("a"), iVal(-20))));
}

static void tst5() {
    environment env;
    env.add_var(name("a"), Int);
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
    std::thread t1([](){ std::cout << "t1: " << mk_int_add_fn().raw() << "\n"; });
    t1.join();
    std::thread t2([](){ std::cout << "t2: " << mk_int_add_fn().raw() << "\n"; });
    t2.join();
    #endif
    std::cout << mk_int_add_fn().raw() << "\n";
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    return has_violations() ? 1 : 0;
}
