/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <string>
#include "util/thread.h"
#include "util/test.h"
#include "util/trace.h"
#include "util/exception.h"
#include "util/interrupt.h"
#include "util/timeit.h"
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "kernel/kernel.h"
#include "kernel/normalizer.h"
#include "kernel/kernel_exception.h"
#include "kernel/type_checker_justification.h"
#include "kernel/io_state.h"
#include "library/printer.h"
#include "library/io_state_stream.h"
#include "library/arith/arith.h"
#include "frontends/lean/frontend.h"
#include "frontends/lua/register_modules.h"
using namespace lean;

expr c(char const * n) { return mk_constant(n); }

static void tst1() {
    environment env;
    expr t0 = Type();
    std::cout << type_check(t0, env) << "\n";
    lean_assert(type_check(t0, env) == Type(level()+1));
    expr f = mk_pi("_", t0, t0);
    std::cout << type_check(f, env) << "\n";
    lean_assert(type_check(f, env) == Type(level()+1));
    level u = env->add_uvar_cnstr("u", level() + 1);
    level v = env->add_uvar_cnstr("v", level() + 1);
    expr g = mk_pi("_", Type(u), Type(v));
    std::cout << type_check(g, env) << "\n";
    lean_assert(type_check(g, env) == Type(max(u+1, v+1)));
    std::cout << type_check(Type(u), env) << "\n";
    lean_assert(type_check(Type(u), env) == Type(u+1));
    std::cout << type_check(mk_lambda("x", Type(u), Var(0)), env) << "\n";
    lean_assert(type_check(mk_lambda("x", Type(u), Var(0)), env) == mk_pi("_", Type(u), Type(u)));
    std::cout << type_check(mk_lambda("Nat", Type(), mk_lambda("n", Var(0), Var(0))), env) << "\n";
    expr nat = c("nat");
    expr T = Fun("nat", Type(),
             Fun("+", mk_arrow(nat, mk_arrow(nat, nat)),
             Fun("m", nat, mk_app({c("+"), c("m"), c("m")}))));
    std::cout << T << "\n";
    std::cout << type_check(T, env) << "\n";
    std::cout << Pi("nat", Type(), mk_arrow(mk_arrow(nat, mk_arrow(nat, nat)), mk_arrow(nat, nat))) << "\n";
    lean_assert(type_check(T, env) == Pi("nat", Type(), mk_arrow(mk_arrow(nat, mk_arrow(nat, nat)), mk_arrow(nat, nat))));
}

static void tst2() {
    try{
        environment env;
        level l1      = env->add_uvar_cnstr("l1", level() + 1);
        expr t0       = Type();
        expr t1       = Type(l1);
        expr F =
            Fun("Nat", t0,
            Fun("Vec", mk_arrow(c("Nat"), t0),
            Fun("n", c("Nat"),
            Fun("len", mk_arrow(mk_app({c("Vec"), c("n")}), c("Nat")),
            Fun("v", mk_app({c("Vec"), c("n")}),
                mk_app({c("len"), c("v")}))))));
        std::cout << F << "\n";
        std::cout << type_check(F, env) << "\n";
    }
    catch (exception & ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

static void tst3() {
    environment env;
    init_test_frontend(env);
    expr f = Fun("a", Bool, mk_eq(Bool, Const("a"), True));
    std::cout << type_check(f, env) << "\n";
    lean_assert(type_check(f, env) == mk_arrow(Bool, Bool));
    expr t = mk_let("a", none_expr(), True, Var(0));
    std::cout << type_check(t, env) << "\n";
}

static void tst4() {
    environment env;
    init_test_frontend(env);
    expr a = mk_eq(Int, iVal(1), iVal(2));
    expr pr   = mk_lambda("x", a, Var(0));
    std::cout << type_check(pr, env) << "\n";
}

static void tst5() {
    environment env;
    init_test_frontend(env);
    env->add_var("P", Bool);
    expr P = Const("P");
    expr H = Const("H");
    unsigned n = 4000;
    expr prop = P;
    expr pr   = H;
    for (unsigned i = 1; i < n; i++) {
        pr   = mk_and_intro_th(P, prop, H, pr);
        prop = And(P, prop);
    }
}

static void tst6() {
    environment env;
    init_test_frontend(env);
    expr A = Const("A");
    expr f = Const("f");
    expr x = Const("x");
    expr t = Fun({A, Type()}, Fun({f, mk_arrow(Int, A)}, Fun({x, Int}, f(x, x))));
    try {
        type_check(t, env);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

static void tst7() {
    environment env;
    init_test_frontend(env);
    expr A = Const(name{"foo", "bla", "bla", "foo"});
    expr f = Const("f");
    expr x = Const("x");
    expr t = Fun({A, Type()}, Fun({f, mk_arrow(Int, mk_arrow(A, mk_arrow(A, mk_arrow(A, mk_arrow(A, mk_arrow(A, A))))))}, Fun({x, Int}, f(x, x))));
    try {
        type_check(t, env);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

static void tst8() {
    environment env;
    init_test_frontend(env);
    env->add_var("P", mk_arrow(Int, mk_arrow(Int, Bool)));
    env->add_var("x", Int);
    expr P = Const("P");
    context c;
    c = extend(c, "P", mk_arrow(Bool, Bool));
    c = extend(c, "P", mk_arrow(Int, Int));
    c = extend(c, "H", Var(1)(True));
    c = extend(c, "x", Bool);
    expr t = P(Const("x"), Var(0));
    try {
        type_check(t, env, c);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

static void tst9() {
    environment env;
    init_test_frontend(env);
    env->add_var("P", mk_arrow(Int, mk_arrow(Int, Bool)));
    env->add_var("x", Int);
    expr P = Const("P");
    context c;
    c = extend(c, "P", mk_arrow(Bool, Bool));
    c = extend(c, "P", Bool, Var(0)(True));
    c = extend(c, "H", Var(1)(True));
    c = extend(c, "x", Bool);
    expr t = P(Const("x"), Var(0));
    try {
        type_check(t, env, c);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

static void tst10() {
    environment env;
    init_test_frontend(env);
    env->add_var("f", mk_arrow(Int, Int));
    env->add_var("b", Int);
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr t1 = Let({{a, f(b)}, {a, f(a)}}, f(a));
    expr t2 = f(f(f(b)));
    std::cout << t1 << " --> " << normalize(t1, env) << "\n";
    expr prop  = mk_eq(Int, t1, t2);
    expr proof = mk_refl_th(Int, t1);
    env->add_theorem("simp_eq", prop, proof);
    std::cout << env->get_object("simp_eq").get_name() << "\n";
}

static void tst11() {
    environment env;
    init_test_frontend(env);
    env->add_var("f", Int >> (Int >> Int));
    env->add_var("a", Int);
    unsigned n = 1000;
    expr f = Const("f");
    expr a = Const("a");
    expr t1 = f(a, a);
    expr b = Const("a");
    expr t2 = f(a, a);
    expr t3 = f(b, b);
    for (unsigned i = 0; i < n; i++) {
        t1 = f(t1, t1);
        t2 = mk_let("x", none_expr(), t2, f(Var(0), Var(0)));
        t3 = f(t3, t3);
    }
    lean_assert(t1 != t2);
    env->add_theorem("eqs1", mk_eq(Int, t1, t2), mk_refl_th(Int, t1));
    env->add_theorem("eqs2", mk_eq(Int, t1, t3), mk_refl_th(Int, t1));
}

static expr mk_big(unsigned depth) {
    if (depth == 0)
        return Const("a");
    else
        return Const("f")(mk_big(depth - 1), mk_big(depth - 1));
}

static void tst12() {
#if !defined(__APPLE__) && defined(LEAN_MULTI_THREAD)
    expr t = mk_big(18);
    environment env;
    init_test_frontend(env);
    env->add_var("f", Int >> (Int >> Int));
    env->add_var("a", Int);
    type_checker checker(env);
    chrono::milliseconds dura(100);
    interruptible_thread thread([&]() {
            try {
                std::cout << checker.check(t) << "\n";
                // Remark: if the following code is reached, we
                // should decrease dura.
                lean_unreachable();
            } catch (interrupted & it) {
                std::cout << "interrupted\n";
            }
        });
    this_thread::sleep_for(dura);
    thread.request_interrupt();
    thread.join();
#endif
}

static void tst13() {
    environment env;
    init_test_frontend(env);
    env->add_var("f", Type() >> Type());
    expr f = Const("f");
    std::cout << type_check(f(Bool), env) << "\n";
    std::cout << type_check(f(mk_eq(Bool, True, False)), env) << "\n";
}

static void tst14() {
    environment env;
    init_test_frontend(env);
    expr f = Const("f");
    expr a = Const("a");
    env->add_var("f", Int >> Int);
    env->add_var("a", Real);
    expr F = f(a);
    type_checker checker(env);
    formatter fmt = mk_simple_formatter();
    io_state st(options(), fmt);
    try {
        std::cout << checker.check(F) << "\n";
    } catch (kernel_exception & ex) {
        regular(st) << ex << "\n";
    }
}

static void tst15() {
    environment env;
    init_test_frontend(env);
    context ctx1, ctx2;
    expr A = Const("A");
    expr vec1 = Const("vec1");
    expr vec2 = Const("vec2");
    env->add_var("vec1", Int  >> (Type() >> Type()));
    env->add_var("vec2", Real >> (Type() >> Type()));
    ctx1 = extend(ctx1, "x", Int,  iVal(1));
    ctx1 = extend(ctx1, "f", Pi({A, Int}, vec1(A, Int)));
    ctx2 = extend(ctx2, "x", Real, rVal(2));
    ctx2 = extend(ctx2, "f", Pi({A, Real}, vec2(A, Real)));
    expr F = Var(0)(Var(1));
    expr F_copy = F;
    type_checker checker(env);
    std::cout << checker.check(F, ctx1) << "\n";
    lean_assert_eq(checker.check(F, ctx1), vec1(Var(1), Int));
    lean_assert_eq(checker.check(F, ctx2), vec2(Var(1), Real));
    // Disable for now
    // lean_assert(is_eqp(checker.check(F, ctx2), checker.check(F, ctx2)));
    // lean_assert(is_eqp(checker.check(F, ctx1), checker.check(F, ctx1)));
    expr r = checker.check(F, ctx1);
    checker.clear();
    lean_assert(!is_eqp(r, checker.check(F, ctx1)));
    r = checker.check(F, ctx1);
    // lean_assert(is_eqp(r, checker.check(F, ctx1)));
}

static void check_justification_msg(justification const & t, char const * expected) {
    formatter fmt = mk_simple_formatter();
    options   opts;
    opts = opts.update({"pp", "indent"}, 2);
    format    r = t.pp(fmt, opts);
    std::cout << r << "\n";
    std::ostringstream strm;
    strm << r;
    lean_assert_eq(strm.str(), std::string(expected));
}

static void tst16() {
    std::cout << "Testing type checker justification objects\n";
    context ctx;
    expr f = Const("f");
    expr a = Const("a");
    expr x = Var(0);
    ctx = extend(ctx, "x", Const("N"));
    check_justification_msg(mk_function_expected_justification(ctx, f(a, x)), "Function expected at\n  f a x#0");
    check_justification_msg(mk_type_expected_justification(ctx, Pi({a, Const("N")}, Var(1))), "Type expected at\n  N -> x#1");
    check_justification_msg(mk_type_expected_justification(ctx, Pi({a, Const("N")}, Var(1)(a))), "Type expected at\n  Pi a : N, (x#1 a#0)");
    check_justification_msg(mk_app_type_match_justification(ctx, f(a, x), 1), "Type of argument 1 must be convertible to the expected type in the application of\n  f\nwith arguments:\n  a\n  x#0");
    check_justification_msg(mk_max_type_justification(ctx, Pi({a, Const("N")}, Var(1))), "Type expected at\n  N -> x#1");
    check_justification_msg(mk_def_type_match_justification(ctx, "foo", f(a, x)), "Type of definition 'foo' must be convertible to expected type.");
}

static void f1(type_checker & tc, expr const & F) {
    metavar_env menv;
    expr m1 = menv->mk_metavar(context(), some_expr(Bool >> Int));
    expr r = tc.check(F, context(), menv);
    lean_assert_eq(r, Int);
}

static void f2(type_checker & tc, expr const & F) {
    metavar_env menv;
    expr m1 = menv->mk_metavar(context(), some_expr(Bool >> Bool));
    expr r = tc.check(F, context(), menv);
    lean_assert_eq(r, Bool);
}

static void tst17() {
    environment env;
    init_test_frontend(env);
    type_checker tc(env);
    expr A = Const("A");
    expr F;
    {
        metavar_env menv;
        expr m1 = menv->mk_metavar();
        F = m1(True);
    }
    expr F2 = F;
    f1(tc, F);
    f2(tc, F);
}

static std::ostream & operator<<(std::ostream & out, buffer<unification_constraint> const & uc) {
    formatter fmt = mk_simple_formatter();
    for (auto c : uc) {
        out << c.pp(fmt, options(), nullptr, true) << "\n";
    }
    return out;
}

static void tst18() {
    environment env;
    init_test_frontend(env);
    type_inferer type_of(env);
    expr f = Const("f");
    expr g = Const("g");
    expr a = Const("a");
    expr b = Const("b");
    expr A = Const("A");
    env->add_var("f", Int >> (Int >> Int));
    lean_assert(type_of(f(a, a)) == Int);
    lean_assert(type_of(f(a)) == Int >> Int);
    lean_assert(is_bool(type_of(And(a, f(a)))));
    lean_assert(type_of(Fun({a, Int}, mk_Int_add(a, iVal(1)))) == Int >> Int);
    lean_assert(type_of(Let({a, iVal(10)}, mk_Int_add(a, b))) == Int);
    lean_assert(type_of(Type()) == Type(level() + 1));
    lean_assert(type_of(Bool) == Type());
    lean_assert(type_of(Pi({a, Type()}, Type(level() + 2))) == Type(level() + 3));
    lean_assert(type_of(Pi({a, Type(level()+4)}, Type(level() + 2))) == Type(level() + 5));
    lean_assert(type_of(Pi({a, Int}, Bool)) == Type());
    env->add_var("g", Pi({A, Type()}, A >> A));
    lean_assert(type_of(g(Int, a)) == Int);
    lean_assert(type_of(g(Fun({a, Type()}, a)(Int), a)) == Fun({a, Type()}, a)(Int));
}

static expr mk_big(unsigned val, unsigned depth) {
    if (depth == 0)
        return iVal(val);
    else
        return mk_Int_add(mk_big(val*2, depth-1), mk_big(val*2 + 1, depth-1));
}

static void tst19() {
    environment env;
    init_test_frontend(env);
    type_inferer type_of(env);
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
            type_of_slow.check(t);
            type_of_slow.clear();
        }
    }
}

static void tst20() {
    environment env;
    init_test_frontend(env);
    context ctx1, ctx2;
    expr A = Const("A");
    expr vec1 = Const("vec1");
    expr vec2 = Const("vec2");
    env->add_var("vec1", Int  >> (Type() >> Type()));
    env->add_var("vec2", Real >> (Type() >> Type()));
    ctx1 = extend(ctx1, "x", Int,  iVal(1));
    ctx1 = extend(ctx1, "f", Pi({A, Int}, vec1(A, Int)));
    ctx2 = extend(ctx2, "x", Real, rVal(2));
    ctx2 = extend(ctx2, "f", Pi({A, Real}, vec2(A, Real)));
    expr F = Var(0)(Var(1));
    expr F_copy = F;
    type_inferer infer(env);
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

static void tst21() {
    environment  env;
    init_test_frontend(env);
    metavar_env menv;
    buffer<unification_constraint> uc;
    type_inferer inferer(env);
    expr list = Const("list");
    expr nil  = Const("nil");
    expr cons = Const("cons");
    expr A    = Const("A");
    env->add_var("list", Type() >> Type());
    env->add_var("nil", Pi({A, Type()}, list(A)));
    env->add_var("cons", Pi({A, Type()}, A >> (list(A) >> list(A))));
    env->add_var("a", Int);
    env->add_var("b", Int);
    env->add_var("n", Nat);
    env->add_var("m", Nat);
    expr a  = Const("a");
    expr b  = Const("b");
    expr n  = Const("n");
    expr m  = Const("m");
    expr m1 = menv->mk_metavar();
    expr m2 = menv->mk_metavar();
    expr m3 = menv->mk_metavar();
    expr A1 = menv->mk_metavar();
    expr A2 = menv->mk_metavar();
    expr A3 = menv->mk_metavar();
    expr A4 = menv->mk_metavar();
    expr F  = cons(A1, m1(a), cons(A2, m2(n), cons(A3, m3(b), nil(A4))));
    std::cout << F << "\n";
    std::cout << inferer(F, context(), menv, uc) << "\n";
    std::cout << uc << "\n";
}

static void tst22() {
    environment  env;
    init_test_frontend(env);
    expr a = mk_arrow(Nat, Bool);
    expr b = mk_arrow(Nat, Nat);
    type_checker tc(env);
    lean_assert(!tc.is_convertible(a, b));
    lean_assert(!tc.is_convertible(b, a));
}

int main() {
    save_stack_info();
    register_modules();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    tst9();
    tst10();
    tst11();
    tst12();
    tst13();
    tst14();
    tst15();
    tst16();
    tst17();
    tst18();
    tst19();
    return has_violations() ? 1 : 0;
    tst20();
    tst21();
    tst22();
    return has_violations() ? 1 : 0;
}
