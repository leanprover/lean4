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
#include "kernel/builtin.h"
#include "kernel/expr_sets.h"
#include "kernel/abstract.h"
#include "kernel/kernel_exception.h"
#include "kernel/printer.h"
#include "library/all/all.h"
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
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type:
    case expr_kind::Value: case expr_kind::MetaVar:
        return 1;
    case expr_kind::App:
        return std::accumulate(begin_args(a), end_args(a), 1,
                               [&](unsigned sum, expr const & arg){ return sum + count_core(arg, s); });
    case expr_kind::Eq:
        return count_core(eq_lhs(a), s) + count_core(eq_rhs(a), s) + 1;
    case expr_kind::Lambda: case expr_kind::Pi:
        return count_core(abst_domain(a), s) + count_core(abst_body(a), s) + 1;
    case expr_kind::Let:
        return count_core(let_value(a), s) + count_core(let_body(a), s) + 1;
    }
    return 0;
}

unsigned count(expr const & a) {
    expr_set s;
    return count_core(a, s);
}

static void tst_church_numbers() {
    environment env;
    env.add_var("t", Type());
    env.add_var("N", Type());
    env.add_var("z", Const("N"));
    env.add_var("s", Const("N"));
    expr N = Const("N");
    expr z = Const("z");
    expr s = Const("s");
    std::cout << normalize(mk_app(zero(), N, s, z), env) << "\n";
    std::cout << normalize(mk_app(one(), N, s, z), env)  << "\n";
    std::cout << normalize(mk_app(two(), N, s, z), env) << "\n";
    std::cout << normalize(mk_app(four(), N, s, z), env) << "\n";
    std::cout << count(normalize(mk_app(four(), N, s, z), env)) << "\n";
    lean_assert(count(normalize(mk_app(four(), N, s, z), env)) == 4 + 2);
    std::cout << normalize(mk_app(mk_app(times(), four(), four()), N, s, z), env) << "\n";
    std::cout << normalize(mk_app(mk_app(power(), two(), four()), N, s, z), env) << "\n";
    lean_assert(count(normalize(mk_app(mk_app(power(), two(), four()), N, s, z), env)) == 16 + 2);
    std::cout << normalize(mk_app(mk_app(times(), two(), mk_app(power(), two(), four())), N, s, z), env) << "\n";
    std::cout << count(normalize(mk_app(mk_app(times(), two(), mk_app(power(), two(), four())), N, s, z), env)) << "\n";
    std::cout << count(normalize(mk_app(mk_app(times(), four(), mk_app(power(), two(), four())), N, s, z), env)) << "\n";
    lean_assert(count(normalize(mk_app(mk_app(times(), four(), mk_app(power(), two(), four())), N, s, z), env)) == 64 + 2);
    expr big = normalize(mk_app(mk_app(power(), two(), mk_app(power(), two(), three())), N, s, z), env);
    std::cout << count(big) << "\n";
    lean_assert(count(big) == 256 + 2);
    expr three = mk_app(plus(), two(), one());
    lean_assert(count(normalize(mk_app(mk_app(power(), three, three), N, s, z), env)) == 27 + 2);
    // expr big2 = normalize(mk_app(mk_app(power(), two(), mk_app(times(), mk_app(plus(), four(), one()), four())), N, s, z), env);
    // std::cout << count(big2) << "\n";
    std::cout << normalize(lam(lam(mk_app(mk_app(times(), four(), four()), N, Var(0), z))), env) << "\n";
}

static void tst1() {
    environment env;
    env.add_var("t", Type());
    expr t = Type();
    env.add_var("f", mk_arrow(t, t));
    expr f = Const("f");
    env.add_var("a", t);
    expr a = Const("a");
    env.add_var("b", t);
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
    expr t = Type();
    env.add_var("f", mk_arrow(t, t));
    expr f = Const("f");
    env.add_var("a", t);
    expr a = Const("a");
    env.add_var("b", t);
    expr b = Const("b");
    env.add_var("h", mk_arrow(t, t));
    expr h = Const("h");
    expr x = Var(0);
    expr y = Var(1);
    lean_assert(normalize(f(x, x), env, extend(context(), name("f"), t, f(a))) == f(f(a), f(a)));
    context c1 = extend(extend(context(), name("f"), t, f(a)), name("h"), t, h(x));
    expr F1 = normalize(f(x, f(x)), env, c1);
    lean_assert(F1 == f(h(f(a)), f(h(f(a)))));
    std::cout << F1 << "\n";
    expr F2 = normalize(mk_lambda("x", t, f(x, f(y))), env, c1);
    std::cout << F2 << "\n";
    lean_assert(F2 == mk_lambda("x", t, f(x, f(h(f(a))))));
    expr F3 = normalize(mk_lambda("y", t, mk_lambda("x", t, f(x, f(y)))), env, c1);
    std::cout << F3 << "\n";
    lean_assert(F3 == mk_lambda("y", t, mk_lambda("x", t, f(x, f(y)))));
    context c2 = extend(extend(context(), name("foo"), t, mk_lambda("x", t, f(x, a))), name("bla"), t, mk_lambda("z", t, h(x, y)));
    expr F4 = normalize(mk_lambda("x", t, f(x, f(y))), env, c2);
    std::cout << F4 << "\n";
    lean_assert(F4 == mk_lambda("x", t, f(x, f(mk_lambda("z", t, h(x, mk_lambda("x", t, f(x, a))))))));
    context c3 = extend(context(), name("x"), t);
    expr f5 = mk_app(mk_lambda("f", t, mk_lambda("z", t, Var(1))), mk_lambda("y", t, Var(1)));
    expr F5 = normalize(f5, env, c3);
    std::cout << f5 << "\n---->\n";
    std::cout << F5 << "\n";
    lean_assert(F5 == mk_lambda("z", t, mk_lambda("y", t, Var(2))));
    context c4 = extend(extend(context(), name("x"), t), name("x2"), t);
    expr F6 = normalize(mk_app(mk_lambda("f", t, mk_lambda("z1", t, mk_lambda("z2", t, mk_app(Var(2), Const("a"))))),
                               mk_lambda("y", t, mk_app(Var(1), Var(2), Var(0)))), env, c4);
    std::cout << F6 << "\n";
    lean_assert(F6 == mk_lambda("z1", t, mk_lambda("z2", t, mk_app(Var(2), Var(3), Const("a")))));
}

static void tst3() {
    environment env = mk_toplevel();
    env.add_var("a", Bool);
    expr t1 = Const("a");
    expr t2 = Const("a");
    expr e = Eq(t1, t2);
    std::cout << e << " --> " << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == Eq(t1, t2));
}

static void tst4() {
    environment env;
    env.add_var("b", Type());
    expr t1 = mk_let("a", none_expr(), Const("b"), mk_lambda("c", Type(), Var(1)(Var(0))));
    std::cout << t1 << " --> " << normalize(t1, env) << "\n";
    lean_assert(normalize(t1, env) == mk_lambda("c", Type(), Const("b")(Var(0))));
}

static expr mk_big(unsigned depth) {
    if (depth == 0)
        return Const("a");
    else
        return Const("f")(mk_big(depth - 1), mk_big(depth - 1));
}

static void tst5() {
#if !defined(__APPLE__) && defined(LEAN_MULTI_THREAD)
    expr t = mk_big(18);
    environment env = mk_toplevel();
    env.add_var("f", Bool >> (Bool >> Bool));
    env.add_var("a", Bool);
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

static void tst6() {
    environment env;
    expr x = Const("x");
    expr t = Fun({x, Type()}, mk_app(x, x));
    expr omega = mk_app(t, t);
    normalizer proc(env, 512);
    try {
        proc(omega);
    } catch (kernel_exception & ex) {
        std::cout << ex.what() << "\n";
    }
}

int main() {
    save_stack_info();
    tst_church_numbers();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    return has_violations() ? 1 : 0;
}
