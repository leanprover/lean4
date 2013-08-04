/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "environment.h"
#include "type_check.h"
#include "arith.h"
#include "normalize.h"
#include "abstract.h"
#include "test.h"
using namespace lean;

static void tst1() {
    environment env;
    expr e = int_value(mpz(10));
    lean_assert(is_int_value(e));
    lean_assert(infer_type(e, env) == int_type());
    std::cout << "e: " << e << "\n";
}

static void tst2() {
    environment env;
    expr e = app(int_add(), int_value(10), int_value(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == int_value(40));
    std::cout << infer_type(int_add(), env) << "\n";
    lean_assert(infer_type(e, env) == int_type());
    lean_assert(infer_type(app(int_add(), int_value(10)), env) == arrow(int_type(), int_type()));
    lean_assert(is_int_add(int_add()));
    lean_assert(!is_int_add(int_mul()));
    lean_assert(is_int_value(normalize(e, env)));
    expr e2 = fun("a", int_type(), app(int_add(), constant("a"), app(int_add(), int_value(10), int_value(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(infer_type(e2, env) == arrow(int_type(), int_type()));
    lean_assert(normalize(e2, env) == fun("a", int_type(), app(int_add(), constant("a"), int_value(40))));
}

static void tst3() {
    environment env;
    expr e = app(int_mul(), int_value(10), int_value(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == int_value(300));
    std::cout << infer_type(int_mul(), env) << "\n";
    lean_assert(infer_type(e, env) == int_type());
    lean_assert(infer_type(app(int_mul(), int_value(10)), env) == arrow(int_type(), int_type()));
    lean_assert(is_int_mul(int_mul()));
    lean_assert(!is_int_mul(int_add()));
    lean_assert(is_int_value(normalize(e, env)));
    expr e2 = fun("a", int_type(), app(int_mul(), constant("a"), app(int_mul(), int_value(10), int_value(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(infer_type(e2, env) == arrow(int_type(), int_type()));
    lean_assert(normalize(e2, env) == fun("a", int_type(), app(int_mul(), constant("a"), int_value(300))));
}

static void tst4() {
    environment env;
    expr e = app(int_sub(), int_value(10), int_value(30));
    std::cout << e << "\n";
    std::cout << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == int_value(-20));
    std::cout << infer_type(int_sub(), env) << "\n";
    lean_assert(infer_type(e, env) == int_type());
    lean_assert(infer_type(app(int_sub(), int_value(10)), env) == arrow(int_type(), int_type()));
    lean_assert(is_int_sub(int_sub()));
    lean_assert(!is_int_sub(int_add()));
    lean_assert(is_int_value(normalize(e, env)));
    expr e2 = fun("a", int_type(), app(int_sub(), constant("a"), app(int_sub(), int_value(10), int_value(30))));
    std::cout << e2 << " --> " << normalize(e2, env) << "\n";
    lean_assert(infer_type(e2, env) == arrow(int_type(), int_type()));
    lean_assert(normalize(e2, env) == fun("a", int_type(), app(int_sub(), constant("a"), int_value(-20))));
}

int main() {
    continue_on_violation(true);
    tst1();
    tst2();
    tst3();
    tst4();
    return has_violations() ? 1 : 0;
}
