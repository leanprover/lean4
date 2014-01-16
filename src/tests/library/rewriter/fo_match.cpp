/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "util/test.h"
#include "util/trace.h"
#include "kernel/abstract.h"
#include "kernel/expr.h"
#include "kernel/metavar.h"
#include "kernel/kernel.h"
#include "library/printer.h"
#include "library/arith/arith.h"
#include "library/arith/nat.h"
#include "library/rewriter/fo_match.h"
#include "library/rewriter/rewriter.h"
using namespace lean;

using std::cout;
using std::pair;
using std::endl;

static bool test_match(expr const & p, expr const & v, unsigned o, subst_map & s) {
    fo_match fm;
    cout << "match(" << p << ", " << endl
         << "      " << v << ", " << endl
         << "      " << o << ", " << s << ")" << endl;
    bool result = fm.match(p, v, o, s);
    cout << "= (" << (result ? "true" : "false") << ", "
              << s << ")" << endl;
    return result;
}

static void match_var_tst1() {
    cout << "--- match_var_tst1() ---" << endl;
    expr f = Var(0);
    expr a = Const("a");
    subst_map s;
    bool result = test_match(f, a, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.find(0)->second, a);
}

static void match_var_tst2() {
    cout << "--- match_var_tst2() ---" << endl;
    expr f = Var(0);
    expr a = Const("a");
    subst_map s;
    bool result = test_match(a, f, 0, s);
    lean_assert_eq(result, false);
    lean_assert(s.find(0) == s.end(), s);
    lean_assert_eq(s.empty(), true)
}

static void match_var_tst3() {
    cout << "--- match_var_tst3() ---" << endl;
    expr f = Var(0);
    expr a = Const("a");
    subst_map s;
    bool result = test_match(f, a, 1, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_var_tst4() {
    cout << "--- match_var_tst4() ---" << endl;
    expr f = Var(0);
    expr a = Const("a");
    subst_map s;
    s.insert(0, a);
    bool result = test_match(f, a, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.find(0)->second, a);
}

static void match_var_tst5() {
    cout << "--- match_var_tst5() ---" << endl;
    expr f = Var(0);
    expr a = Const("a");
    expr b = Const("b");
    subst_map s;
    s.insert(0, b);
    bool result = test_match(f, a, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.find(0)->second, b);
}

static void match_constant_tst1() {
    cout << "--- match_constant_tst1() ---" << endl;
    expr a = Const("a");
    expr b = Const("b");
    subst_map s;
    bool result = test_match(a, a, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.empty(), true);
}

static void match_constant_tst2() {
    cout << "--- match_constant_tst2() ---" << endl;
    expr a = Const("a");
    expr b = Const("b");
    subst_map s;
    bool result = test_match(a, b, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_value_tst1() {
    cout << "--- match_value_tst1() ---" << endl;
    expr zero = nVal(0);
    expr a = Const("a");
    subst_map s;
    bool result = test_match(zero, a, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_value_tst2() {
    cout << "--- match_value_tst2() ---" << endl;
    expr zero = nVal(0);
    expr a = Const("a");
    subst_map s;
    bool result = test_match(zero, zero, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.empty(), true);
}

static void match_lambda_tst1() {
    cout << "--- match_lambda_tst1() ---" << endl;
    expr a  = Const("a");
    expr zero = nVal(0);
    expr x  = Var(0);
    expr y  = Var(1);
    expr ty = Type();
    expr fun1 = mk_lambda("x", ty, x(y));
    expr fun2 = mk_lambda("x", ty, x(zero));
    subst_map s;
    bool result = test_match(fun1, fun2, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.find(0)->second, zero);
    lean_assert_eq(s.size(), 1);
}

static void match_lambda_tst2() {
    cout << "--- match_lambda_tst2() ---" << endl;
    expr a  = Const("a");
    expr x  = Var(0);
    expr y  = Var(1);
    expr ty = Type();
    expr fun1 = mk_lambda("x", ty, x(y));
    subst_map s;
    bool result = test_match(fun1, a, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_lambda_tst3() {
    cout << "--- match_lambda_tst3() ---" << endl;
    expr a  = Const("a");
    expr zero = nVal(0);
    expr x  = Var(0);
    expr y  = Var(1);
    expr fun1 = mk_lambda("x", Int, x(y));
    expr fun2 = mk_lambda("x", Nat, x(zero));
    subst_map s;
    bool result = test_match(fun1, fun2, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_lambda_tst4() {
    cout << "--- match_lambda_tst4() ---" << endl;
    expr a  = Const("a");
    expr zero = nVal(0);
    expr x  = Var(0);
    expr y  = Var(1);
    expr ty = Type();
    expr fun1 = mk_lambda("x", ty, x(y, y));
    expr fun2 = mk_lambda("x", ty, x(zero));
    subst_map s;
    bool result = test_match(fun1, fun2, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}


static void match_pi_tst1() {
    cout << "--- match_pi_tst1() ---" << endl;
    expr a  = Const("a");
    expr zero = nVal(0);
    expr x  = Var(0);
    expr y  = Var(1);
    expr ty = Type();
    expr fun1 = mk_pi("x", ty, x(y));
    expr fun2 = mk_pi("x", ty, x(zero));
    subst_map s;
    bool result = test_match(fun1, fun2, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.find(0)->second, zero);
    lean_assert_eq(s.size(), 1);
}

static void match_pi_tst2() {
    cout << "--- match_pi_tst2() ---" << endl;
    expr a  = Const("a");
    expr x  = Var(0);
    expr y  = Var(1);
    expr ty = Type();
    expr fun1 = mk_pi("x", ty, x(y));
    subst_map s;
    bool result = test_match(fun1, a, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_pi_tst3() {
    cout << "--- match_pi_tst3() ---" << endl;
    expr a  = Const("a");
    expr zero = nVal(0);
    expr x  = Var(0);
    expr y  = Var(1);
    expr fun1 = mk_pi("x", Int, x(y));
    expr fun2 = mk_pi("x", Nat, x(zero));
    subst_map s;
    bool result = test_match(fun1, fun2, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_pi_tst4() {
    cout << "--- match_pi_tst4() ---" << endl;
    expr a  = Const("a");
    expr zero = nVal(0);
    expr x  = Var(0);
    expr y  = Var(1);
    expr ty = Type();
    expr fun1 = mk_pi("x", ty, x(y, y));
    expr fun2 = mk_pi("x", ty, x(zero));
    subst_map s;
    bool result = test_match(fun1, fun2, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_type_tst1() {
    cout << "--- match_type_tst1() ---" << endl;
    expr t0 = Type();
    subst_map s;
    bool result = test_match(t0, t0, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.empty(), true);
}

static void match_type_tst2() {
    cout << "--- match_type_tst2() ---" << endl;
    expr t0 = Type();
    expr t1 = Type(level()+1);
    subst_map s;
    bool result = test_match(t0, t1, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_let_tst1() {
    cout << "--- match_let_tst1() ---" << endl;
    expr l = mk_let("a", Type(), Const("b"), Var(0));
    subst_map s;
    bool result = test_match(l, l, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.empty(), true);
}

static void match_let_tst2() {
    cout << "--- match_let_tst2() ---" << endl;
    expr t = mk_eq(Const("A"), Const("a"), Const("b"));
    expr l = mk_let("a", Type(), Const("b"), Var(0));
    subst_map s;
    bool result = test_match(l, t, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_let_tst3() {
    cout << "--- match_let_tst3() ---" << endl;
    expr t = mk_eq(Const("A"), Const("a"), Const("b"));
    expr l1 = mk_let("a", Var(0), Const("b"), Var(0));
    expr l2 = mk_let("a", Int, Const("b"), Var(0));
    subst_map s;
    bool result = test_match(l1, l2, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.find(0)->second, Int);
    lean_assert_eq(s.size(), 1);
}

static void match_let_tst4() {
    cout << "--- match_let_tst4() ---" << endl;
    expr t = mk_eq(Const("A"), Const("a"), Const("b"));
    expr l1 = mk_let("a", Nat, Const("b"), Var(0));
    expr l2 = mk_let("a", Int, Const("b"), Var(0));
    subst_map s;
    bool result = test_match(l1, l2, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_let_tst5() {
    cout << "--- match_let_tst5() ---" << endl;
    expr t = mk_eq(Const("A"), Const("a"), Const("b"));
    expr l1 = mk_let("a", Int, Var(3), Var(0));
    expr l2 = mk_let("a", Int, Const("b"), Const("b"));
    subst_map s;
    bool result = test_match(l1, l2, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_let_tst6() {
    cout << "--- match_let_tst6() ---" << endl;
    expr t = mk_eq(Const("A"), Const("a"), Const("b"));
    expr l1 = mk_let("a", Var(0), Var(1), Var(0));
    expr l2 = mk_let("a", Int, Const("b"), Const("b"));
    subst_map s;
    bool result = test_match(l1, l2, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_let_tst7() {
    cout << "--- match_let_tst7() ---" << endl;
    expr t = mk_eq(Const("A"), Const("a"), Const("b"));
    expr l1 = mk_let("a", Var(0), Var(1), Var(0));
    expr l2 = mk_let("a", Int, Const("b"), Var(0));
    subst_map s;
    bool result = test_match(l1, l2, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.find(0)->second, Int);
    lean_assert_eq(s.find(1)->second, Const("b"));
    lean_assert_eq(s.size(), 2);
}

static void match_let_tst8() {
    cout << "--- match_let_tst8() ---" << endl;
    expr t = mk_eq(Const("A"), Const("a"), Const("b"));
    expr l1 = mk_let("a", Nat, Var(1), Var(0));
    expr l2 = mk_let("a", Int, Const("b"), Var(0));
    subst_map s;
    bool result = test_match(l1, l2, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_let_tst9() {
    cout << "--- match_let_tst9() ---" << endl;
    expr t = mk_eq(Const("A"), Const("a"), Const("b"));
    expr l1 = mk_let("a", Var(0), Var(0), Var(0));
    expr l2 = mk_let("a", Nat, Const("b"), Const("a"));
    subst_map s;
    bool result = test_match(l1, l2, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_eq_tst1() {
    cout << "--- match_eq_tst1() ---" << endl;
    expr x = Var(0);
    expr f = Const("f");
    expr a = Const("a");
    subst_map s;
    bool result = test_match(mk_eq(Const("A"), x, a), mk_eq(Const("A"), f, a), 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.find(0)->second, f);
    lean_assert_eq(s.size(), 1);
}

static void match_eq_tst2() {
    cout << "--- match_eq_tst2() ---" << endl;
    expr x = Var(0);
    expr f = Const("f");
    expr a = Const("a");
    subst_map s;
    bool result = test_match(mk_eq(Nat, mk_Nat_add(x, a), x), mk_eq(Nat, mk_Nat_add(f, a), f), 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.find(0)->second, f);
    lean_assert_eq(s.size(), 1);
}

static void match_eq_tst3() {
    cout << "--- match_eq_tst3() ---" << endl;
    expr x = Var(0);
    expr f = Const("f");
    expr a = Const("a");
    subst_map s;
    bool result = test_match(mk_eq(Nat, mk_Nat_add(x, a), x), f, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.empty(), true);
}

static void match_metavar_tst1() {
    cout << "--- match_metavar_tst1() ---" << endl;
    metavar_env menv;
    expr m1 = menv->mk_metavar();
    expr m2 = menv->mk_metavar();
    expr f = Const("f");
    subst_map s;
    bool result = test_match(m1, m1, 0, s);
    lean_assert_eq(result, true);
    lean_assert_eq(s.size(), 0);
}

static void match_metavar_tst2() {
    cout << "--- match_metavar_tst2() ---" << endl;
    metavar_env menv;
    expr m1 = menv->mk_metavar();
    expr m2 = menv->mk_metavar();
    expr f = Const("f");
    subst_map s;
    bool result = test_match(m1, m2, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.size(), 0);
}

static void match_metavar_tst3() {
    cout << "--- match_metavar_tst3() ---" << endl;
    metavar_env menv;
    expr m1 = menv->mk_metavar();
    expr f = Const("f");
    subst_map s;
    bool result = test_match(m1, f, 0, s);
    lean_assert_eq(result, false);
    lean_assert_eq(s.size(), 0);
}

int main() {
    save_stack_info();
    match_var_tst1();
    match_var_tst2();
    match_var_tst3();
    match_var_tst4();
    match_var_tst5();
    match_constant_tst1();
    match_constant_tst2();
    match_value_tst1();
    match_value_tst2();
    match_lambda_tst1();
    match_lambda_tst2();
    match_lambda_tst3();
    match_lambda_tst4();
    match_pi_tst1();
    match_pi_tst2();
    match_pi_tst3();
    match_pi_tst4();
    match_type_tst1();
    match_type_tst2();
    match_let_tst1();
    match_let_tst2();
    match_let_tst3();
    match_let_tst4();
    match_let_tst5();
    match_let_tst6();
    match_let_tst7();
    match_let_tst8();
    match_let_tst9();
    match_eq_tst1();
    match_eq_tst2();
    match_eq_tst3();
    match_metavar_tst1();
    match_metavar_tst2();
    match_metavar_tst3();
    return has_violations() ? 1 : 0;
}
