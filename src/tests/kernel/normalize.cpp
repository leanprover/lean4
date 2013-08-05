/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "normalize.h"
#include "builtin.h"
#include "trace.h"
#include "test.h"
#include "sets.h"
using namespace lean;

expr normalize(expr const & e) {
    environment env;
    return normalize(e, env);
}

static void eval(expr const & e, environment & env) { std::cout << e << " --> " << normalize(e, env) << "\n"; }
static expr t() { return constant("t"); }
static expr lam(expr const & e) { return lambda("_", t(), e); }
static expr lam(expr const & t, expr const & e) { return lambda("_", t, e); }
static expr v(unsigned i) { return var(i); }
static expr zero() {
    // fun (t : T) (s : t -> t) (z : t) z
    return lam(t(), lam(arrow(v(0), v(0)), lam(v(1), v(0))));
}
static expr one()  {
    // fun (t : T) (s : t -> t) s
    return lam(t(), lam(arrow(v(0), v(0)), v(0)));
}
static expr num() { return constant("num"); }
static expr plus() {
    //  fun (m n : numeral) (A : Type 0) (f : A -> A) (x : A) => m A f (n A f x).
    expr x = v(0), f = v(1), A = v(2), n = v(3), m = v(4);
    expr body = m(A, f, n(A, f, x));
    return lam(num(), lam(num(), lam(t(), lam(arrow(v(0), v(0)), lam(v(1), body)))));
}
static expr two() { return app(plus(), one(), one()); }
static expr three() { return app(plus(), two(), one()); }
static expr four() { return app(plus(), two(), two()); }
static expr times() {
    // fun (m n : numeral) (A : Type 0) (f : A -> A) (x : A) => m A (n A f) x.
    expr x = v(0), f = v(1), A = v(2), n = v(3), m = v(4);
    expr body = m(A, n(A, f), x);
    return lam(num(), lam(num(), lam(t(), lam(arrow(v(0), v(0)), lam(v(1), body)))));
}
static expr power() {
    // fun (m n : numeral) (A : Type 0) => m (A -> A) (n A).
    expr A = v(0), n = v(1), m = v(2);
    expr body = n(arrow(A, A), m(A));
    return lam(num(), lam(num(), lam(arrow(v(0), v(0)), body)));
}

unsigned count_core(expr const & a, expr_set & s) {
    if (s.find(a) != s.end())
        return 0;
    s.insert(a);
    switch (a.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
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
    env.add_fact("t", type(level()));
    env.add_fact("N", type(level()));
    env.add_fact("z", constant("N"));
    env.add_fact("s", constant("N"));
    expr N = constant("N");
    expr z = constant("z");
    expr s = constant("s");
    std::cout << normalize(app(zero(), N, s, z), env) << "\n";
    std::cout << normalize(app(one(), N, s, z), env)  << "\n";
    std::cout << normalize(app(two(), N, s, z), env) << "\n";
    std::cout << normalize(app(four(), N, s, z), env) << "\n";
    std::cout << count(normalize(app(four(), N, s, z), env)) << "\n";
    lean_assert(count(normalize(app(four(), N, s, z), env)) == 4 + 2);
    std::cout << normalize(app(app(times(), four(), four()), N, s, z), env) << "\n";
    std::cout << normalize(app(app(power(), two(), four()), N, s, z), env) << "\n";
    lean_assert(count(normalize(app(app(power(), two(), four()), N, s, z), env)) == 16 + 2);
    std::cout << normalize(app(app(times(), two(), app(power(), two(), four())), N, s, z), env) << "\n";
    std::cout << count(normalize(app(app(times(), two(), app(power(), two(), four())), N, s, z), env)) << "\n";
    std::cout << count(normalize(app(app(times(), four(), app(power(), two(), four())), N, s, z), env)) << "\n";
    lean_assert(count(normalize(app(app(times(), four(), app(power(), two(), four())), N, s, z), env)) == 64 + 2);
    expr big = normalize(app(app(power(), two(), app(power(), two(), three())), N, s, z), env);
    std::cout << count(big) << "\n";
    lean_assert(count(big) == 256 + 2);
    expr three = app(plus(), two(), one());
    lean_assert(count(normalize(app(app(power(), three, three), N, s, z), env)) == 27 + 2);
    // expr big2 = normalize(app(app(power(), two(), app(times(), app(plus(), four(), one()), four())), N, s, z), env);
    // std::cout << count(big2) << "\n";
    std::cout << normalize(lam(lam(app(app(times(), four(), four()), N, var(0), z))), env) << "\n";
}

static void tst1() {
    environment env;
    env.add_fact("t", type(level()));
    expr t = type(level());
    env.add_fact("f", arrow(t, t));
    expr f = constant("f");
    env.add_fact("a", t);
    expr a = constant("a");
    env.add_fact("b", t);
    expr b = constant("b");
    expr x = var(0);
    expr y = var(1);
    eval(app(lambda("x", t, x), a), env);
    eval(app(lambda("x", t, x), a, b), env);
    eval(lambda("x", t, f(x)), env);
    eval(lambda("y", t, lambda("x", t, f(y, x))), env);
    eval(app(lambda("x", t,
                    app(lambda("f", t,
                               app(var(0), b)),
                        lambda("g", t, f(var(1))))),
             a), env);
    expr l01 = lam(v(0)(v(1)));
    expr l12 = lam(lam(v(1)(v(2))));
    eval(lam(l12(l01)), env);
    lean_assert(normalize(lam(l12(l01)), env) == lam(lam(v(1)(v(1)))));
}

static void tst2() {
    environment env;
    expr t = type(level());
    env.add_fact("f", arrow(t, t));
    expr f = constant("f");
    env.add_fact("a", t);
    expr a = constant("a");
    env.add_fact("b", t);
    expr b = constant("b");
    env.add_fact("h", arrow(t, t));
    expr h = constant("h");
    expr x = var(0);
    expr y = var(1);
    lean_assert(normalize(f(x,x), env, extend(context(), name("f"), t, f(a))) == f(f(a), f(a)));
    context c1 = extend(extend(context(), name("f"), t, f(a)), name("h"), t, h(x));
    expr F1 = normalize(f(x,f(x)), env, c1);
    lean_assert(F1 == f(h(f(a)), f(h(f(a)))));
    std::cout << F1 << "\n";
    expr F2 = normalize(lambda("x", t, f(x, f(y))), env, c1);
    std::cout << F2 << "\n";
    lean_assert(F2 == lambda("x", t, f(x, f(h(f(a))))));
    expr F3 = normalize(lambda("y", t, lambda("x", t, f(x, f(y)))), env, c1);
    std::cout << F3 << "\n";
    lean_assert(F3 == lambda("y", t, lambda("x", t, f(x, f(y)))));
    context c2 = extend(extend(context(), name("foo"), t, lambda("x", t, f(x, a))), name("bla"), t, lambda("z", t, h(x,y)));
    expr F4 = normalize(lambda("x", t, f(x, f(y))), env, c2);
    std::cout << F4 << "\n";
    lean_assert(F4 == lambda("x", t, f(x, f(lambda("z", t, h(x,lambda("x", t, f(x, a))))))));
    context c3 = extend(context(), name("x"), t);
    expr f5 = app(lambda("f", t, lambda("z", t, var(1))), lambda("y", t, var(1)));
    expr F5 = normalize(f5, env, c3);
    std::cout << f5 << "\n---->\n";
    std::cout << F5 << "\n";
    lean_assert(F5 == lambda("z", t, lambda("y", t, var(2))));
    context c4 = extend(extend(context(), name("x"), t), name("x2"), t);
    expr F6 = normalize(app(lambda("f", t, lambda("z1", t, lambda("z2", t, app(var(2), constant("a"))))),
                            lambda("y", t, app(var(1), var(2), var(0)))), env, c4);
    std::cout << F6 << "\n";
    lean_assert(F6 == lambda("z1", t, lambda("z2", t, app(var(2), var(3), constant("a")))));
}

static void tst3() {
    environment env;
    env.add_fact("a", bool_type());
    expr t1 = constant("a");
    expr t2 = constant("a");
    expr e = eq(t1, t2);
    std::cout << e << " --> " << normalize(e, env) << "\n";
    lean_assert(normalize(e, env) == bool_value(true));
}

static void tst4() {
    environment env;
    env.add_fact("b", type(level()));
    expr t1 = let("a", constant("b"), lambda("c", type(), var(1)(var(0))));
    std::cout << t1 << " --> " << normalize(t1, env) << "\n";
    lean_assert(normalize(t1, env) == lambda("c", type(), constant("b")(var(0))));
}

int main() {
    // continue_on_violation(true);
    tst_church_numbers();
    tst1();
    tst2();
    tst3();
    tst4();
    return has_violations() ? 1 : 0;
}
