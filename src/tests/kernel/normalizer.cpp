/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/thread.h"
#include "util/test.h"
#include "util/trace.h"
#include "util/exception.h"
#include "util/interrupt.h"
#include "kernel/normalizer.h"
#include "kernel/expr_sets.h"
#include "kernel/abstract.h"
#include "kernel/kernel_exception.h"
#include "kernel/free_vars.h"
using namespace lean;

expr normalize(expr const & e) {
    environment env;
    return normalize(e, env);
}

static void eval(expr const & e, environment & env) { std::cout << e << " --> " << normalize(e, env) << "\n"; }
static expr t() { return Const("t"); }
static expr lam(expr const & e) { return mk_lambda("_", t(), e); }
static expr lam(expr const & t, expr const & e) { return mk_lambda("_", t, e); }
static expr v(unsigned i) { return Var(i); }
static expr zero() {
    // fun (t : T) (s : t -> t) (z : t) z
    return lam(t(), lam(mk_arrow(v(0), v(0)), lam(v(1), v(0))));
}
static expr one()  {
    // fun (t : T) (s : t -> t) s
    return lam(t(), lam(mk_arrow(v(0), v(0)), v(0)));
}
static expr num() { return Const("num"); }
static expr plus() {
    //  fun (m n : numeral) (A : Type 0) (f : A -> A) (x : A) => m A f (n A f x).
    expr x = v(0), f = v(1), A = v(2), n = v(3), m = v(4);
    expr body = m(A, f, n(A, f, x));
    return lam(num(), lam(num(), lam(t(), lam(mk_arrow(v(0), v(0)), lam(v(1), body)))));
}
static expr two() { return mk_app({plus(), one(), one()}); }
static expr three() { return mk_app({plus(), two(), one()}); }
static expr four() { return mk_app({plus(), two(), two()}); }
static expr times() {
    // fun (m n : numeral) (A : Type 0) (f : A -> A) (x : A) => m A (n A f) x.
    expr x = v(0), f = v(1), A = v(2), n = v(3), m = v(4);
    expr body = m(A, n(A, f), x);
    return lam(num(), lam(num(), lam(t(), lam(mk_arrow(v(0), v(0)), lam(v(1), body)))));
}
static expr power() {
    // fun (m n : numeral) (A : Type 0) => m (A -> A) (n A).
    expr A = v(0), n = v(1), m = v(2);
    expr body = n(mk_arrow(A, A), m(A));
    return lam(num(), lam(num(), lam(mk_arrow(v(0), v(0)), body)));
}

unsigned count_core(expr const & a, expr_set & s) {
    if (s.find(a) != s.end())
        return 0;
    s.insert(a);
    switch (a.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::Meta: case expr_kind::Local:   case expr_kind::Macro:
        return 1;
    case expr_kind::App:
        return count_core(app_fn(a), s) + count_core(app_arg(a), s) + 1;
    case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Sigma:
        return count_core(binder_domain(a), s) + count_core(binder_body(a), s) + 1;
    case expr_kind::Let:
        return count_core(let_value(a), s) + count_core(let_body(a), s) + 1;
    case expr_kind::Fst: case expr_kind::Snd:
        return count_core(proj_arg(a), s) + 1;
    case expr_kind::Pair:
        return count_core(pair_first(a), s) + count_core(pair_second(a), s) + count_core(pair_type(a), s) + 1;
    }
    return 0;
}

unsigned count(expr const & a) {
    expr_set s;
    return count_core(a, s);
}

static void tst_church_numbers() {
    environment env;
    env->add_var("t", Type);
    env->add_var("N", Type);
    env->add_var("z", Const("N"));
    env->add_var("s", Const("N"));
    expr N = Const("N");
    expr z = Const("z");
    expr s = Const("s");
    std::cout << normalize(mk_app(zero(), N, s, z), env) << "\n";
    std::cout << normalize(mk_app(one(), N, s, z), env)  << "\n";
    std::cout << normalize(mk_app(two(), N, s, z), env) << "\n";
    std::cout << normalize(mk_app(four(), N, s, z), env) << "\n";
    std::cout << count(normalize(mk_app(four(), N, s, z), env)) << "\n";
    lean_assert_eq(count(normalize(mk_app(four(), N, s, z), env)), 15);
    std::cout << normalize(mk_app(mk_app(times(), four(), four()), N, s, z), env) << "\n";
    std::cout << normalize(mk_app(mk_app(power(), two(), four()), N, s, z), env) << "\n";
    lean_assert_eq(count(normalize(mk_app(mk_app(power(), two(), four()), N, s, z), env)), 51);
    std::cout << normalize(mk_app(mk_app(times(), two(), mk_app(power(), two(), four())), N, s, z), env) << "\n";
    std::cout << normalize(mk_app(mk_app(times(), four(), mk_app(power(), two(), four())), N, s, z), env) << "\n";
    std::cout << count(normalize(mk_app(mk_app(times(), two(), mk_app(power(), two(), four())), N, s, z), env)) << "\n";
    std::cout << count(normalize(mk_app(mk_app(times(), four(), mk_app(power(), two(), four())), N, s, z), env)) << "\n";
    lean_assert_eq(count(normalize(mk_app(mk_app(times(), four(), mk_app(power(), two(), four())), N, s, z), env)), 195);
    expr big = normalize(mk_app(mk_app(power(), two(), mk_app(power(), two(), three())), N, s, z), env);
    std::cout << count(big) << "\n";
    lean_assert_eq(count(big), 771);
    expr three = mk_app(plus(), two(), one());
    lean_assert_eq(count(normalize(mk_app(mk_app(power(), three, three), N, s, z), env)), 84);
    // expr big2 = normalize(mk_app(mk_app(power(), two(), mk_app(times(), mk_app(plus(), four(), one()), four())), N, s, z), env);
    // std::cout << count(big2) << "\n";
    std::cout << normalize(lam(lam(mk_app(mk_app(times(), four(), four()), N, Var(0), z))), env) << "\n";
}

static void tst1() {
    environment env;
    env->add_var("t", Type);
    expr t = Type;
    env->add_var("f", mk_arrow(t, t));
    expr f = Const("f");
    env->add_var("a", t);
    expr a = Const("a");
    env->add_var("b", t);
    expr b = Const("b");
    expr x = Var(0);
    expr y = Var(1);
    eval(mk_app(mk_lambda("x", t, x), a), env);
    eval(mk_app(mk_lambda("x", t, x), a, b), env);
    eval(mk_lambda("x", t, f(x)), env);
    eval(mk_lambda("y", t, mk_lambda("x", t, f(y, x))), env);
    eval(mk_app(mk_lambda("x", t,
                    mk_app(mk_lambda("f", t,
                               mk_app(Var(0), b)),
                        mk_lambda("g", t, f(Var(1))))),
             a), env);
    expr l01 = lam(v(0)(v(1)));
    expr l12 = lam(lam(v(1)(v(2))));
    eval(lam(l12(l01)), env);
    lean_assert(normalize(lam(l12(l01)), env) == lam(lam(v(1)(v(1)))));
}

static void tst2() {
    environment env;
    env->add_var("b", Type);
    expr t1 = mk_let("a", Type, Const("b"), mk_lambda("c", Type, Var(1)(Var(0))));
    std::cout << t1 << " --> " << normalize(t1, env) << "\n";
    lean_assert(normalize(t1, env) == mk_lambda("c", Type, Const("b")(Var(0))));
}

static expr mk_big(unsigned depth) {
    if (depth == 0)
        return Const("a");
    else
        return Const("f")(mk_big(depth - 1), mk_big(depth - 1));
}

static void tst3() {
#if !defined(__APPLE__) && defined(LEAN_MULTI_THREAD)
    expr t = mk_big(18);
    environment env;
    env->add_var("f", Bool >> (Bool >> Bool));
    env->add_var("a", Bool);
    normalizer proc(env);
    chrono::milliseconds dura(50);
    interruptible_thread thread([&]() {
            try {
                proc(t);
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

static void tst4() {
    environment env;
    expr x = Const("x");
    expr t = Fun({x, Type}, mk_app(x, x));
    expr omega = mk_app(t, t);
    normalizer proc(env, 512);
    try {
        proc(omega);
    } catch (kernel_exception & ex) {
        std::cout << ex.what() << "\n";
    }
}

static void tst5() {
    environment env;
    expr f = Const("f");
    env->add_var("f", Type >> (Type >> Type));
    expr x = Const("x");
    expr v = Const("v");
    expr F = Fun({x, Type}, Let(v, Type, Bool, f(x, v)));
    expr N = normalizer(env)(F);
    std::cout << F << " ==> " << N << "\n";
    lean_assert_eq(N, Fun({x, Type}, f(x, Bool)));
}

int main() {
    save_stack_info();
    tst_church_numbers();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    return has_violations() ? 1 : 0;
}
