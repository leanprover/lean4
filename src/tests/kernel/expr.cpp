/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "expr.h"
#include "sets.h"
#include "max_sharing.h"
#include "free_vars.h"
#include "test.h"
#include "abstract.h"
#include "instantiate.h"
#include "deep_copy.h"
using namespace lean;

void tst1() {
    expr a;
    a = numeral(mpz(10));
    expr f;
    f = var(0);
    expr fa = f(a);
    std::cout << fa << "\n";
    std::cout << fa(a) << "\n";
    lean_assert(eqp(arg(fa, 0), f));
    lean_assert(eqp(arg(fa, 1), a));
    lean_assert(!eqp(fa, f(a)));
    lean_assert(app(fa, a) == f(a, a));
    std::cout << fa(fa, fa) << "\n";
    std::cout << lambda("x", prop(), var(0)) << "\n";
    lean_assert(f(a)(a) == f(a, a));
    lean_assert(f(a(a)) != f(a, a));
    lean_assert(lambda("x", prop(), var(0)) == lambda("y", prop(), var(0)));
    std::cout << pi("x", prop(), var(0)) << "\n";
}

expr mk_dag(unsigned depth, bool _closed = false) {
    expr f = constant("f");
    expr a = _closed ? constant("a") : var(0);
    while (depth > 0) {
        depth--;
        a = f(a, a);
    }
    return a;
}

unsigned depth1(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral:
        return 1;
    case expr_kind::App: {
        unsigned m = 0;
        for (expr const & a : args(e))
            m = std::max(m, depth1(a));
        return m + 1;
    }
    case expr_kind::Lambda: case expr_kind::Pi:
        return std::max(depth1(abst_type(e)), depth1(abst_body(e))) + 1;
    }
    return 0;
}

// This is the fastest depth implementation in this file.
unsigned depth2(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral:
        return 1;
    case expr_kind::App:
        return
            std::accumulate(begin_args(e), end_args(e), 0,
                            [](unsigned m, expr const & arg){ return std::max(depth2(arg), m); })
            + 1;
    case expr_kind::Lambda: case expr_kind::Pi:
        return std::max(depth2(abst_type(e)), depth2(abst_body(e))) + 1;
    }
    return 0;
}

// This is the slowest depth implementation in this file.
unsigned depth3(expr const & e) {
    static std::vector<std::pair<expr const *, unsigned>> todo;
    unsigned m = 0;
    todo.push_back(std::make_pair(&e, 0));
    while (!todo.empty()) {
        auto const & p = todo.back();
        expr const & e = *(p.first);
        unsigned c     = p.second + 1;
        todo.pop_back();
        switch (e.kind()) {
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral:
            m = std::max(c, m);
            break;
        case expr_kind::App: {
            unsigned num = num_args(e);
            for (unsigned i = 0; i < num; i++)
                todo.push_back(std::make_pair(&arg(e, i), c));
            break;
        }
        case expr_kind::Lambda: case expr_kind::Pi:
            todo.push_back(std::make_pair(&abst_type(e), c));
            todo.push_back(std::make_pair(&abst_body(e), c));
            break;
        }
    }
    return m;
}

void tst2() {
    expr r1 = mk_dag(20);
    expr r2 = mk_dag(20);
    lean_verify(r1 == r2);
    std::cout << depth2(r1) << "\n";
    lean_verify(depth2(r1) == 21);
}

expr mk_big(expr f, unsigned depth, unsigned val) {
    if (depth == 1)
        return constant(name(val));
    else
        return f(mk_big(f, depth - 1, val << 1), mk_big(f, depth - 1, (val << 1) + 1));
}

void tst3() {
    expr f = constant("f");
    expr r1 = mk_big(f, 18, 0);
    expr r2 = mk_big(f, 18, 0);
    lean_verify(r1 == r2);
}

void tst4() {
    expr f = constant("f");
    expr a = var(0);
    for (unsigned i = 0; i < 10000; i++) {
        a = f(a);
    }
}

expr mk_redundant_dag(expr f, unsigned depth) {
    if (depth == 0)
        return var(0);
    else
        return f(mk_redundant_dag(f, depth - 1), mk_redundant_dag(f, depth - 1));
}


unsigned count_core(expr const & a, expr_set & s) {
    if (s.find(a) != s.end())
        return 0;
    s.insert(a);
    switch (a.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral:
        return 1;
    case expr_kind::App:
        return std::accumulate(begin_args(a), end_args(a), 1,
                          [&](unsigned sum, expr const & arg){ return sum + count_core(arg, s); });
    case expr_kind::Lambda: case expr_kind::Pi:
        return count_core(abst_type(a), s) + count_core(abst_body(a), s) + 1;
    }
    return 0;
}

unsigned count(expr const & a) {
    expr_set s;
    return count_core(a, s);
}

void tst5() {
    expr f  = constant("f");
    {
        expr r1 = mk_redundant_dag(f, 5);
        expr r2 = max_sharing(r1);
        std::cout << "count(r1): " << count(r1) << "\n";
        std::cout << "count(r2): " << count(r2) << "\n";
        lean_assert(r1 == r2);
    }
    {
        expr r1 = mk_redundant_dag(f, 16);
        expr r2 = max_sharing(r1);
        lean_assert(r1 == r2);
    }
}

void tst6() {
    expr f = constant("f");
    expr r = mk_redundant_dag(f, 12);
    for (unsigned i = 0; i < 1000; i++) {
        r = max_sharing(r);
    }
    r = mk_big(f, 16, 0);
    for (unsigned i = 0; i < 1000000; i++) {
        r = max_sharing(r);
    }
}

void tst7() {
    expr f  = constant("f");
    expr v  = var(0);
    expr a1 = max_sharing(f(v,v));
    expr a2 = max_sharing(f(v,v));
    lean_assert(!eqp(a1, a2));
    expr b  = max_sharing(f(a1, a2));
    lean_assert(eqp(arg(b, 1), arg(b, 2)));
}

void tst8() {
    expr f = constant("f");
    expr x = var(0);
    expr a = constant("a");
    expr n = numeral(mpz(10));
    expr p = prop();
    expr y = var(1);
    lean_assert(closed(a));
    lean_assert(!closed(x));
    lean_assert(closed(f));
    lean_assert(!closed(f(x)));
    lean_assert(closed(lambda("x", p, x)));
    lean_assert(!closed(lambda("x", x, x)));
    lean_assert(!closed(lambda("x", p, y)));
    lean_assert(closed(f(f(f(a)))));
    lean_assert(closed(lambda("x", p, f(f(f(a))))));
    lean_assert(closed(pi("x", p, x)));
    lean_assert(!closed(pi("x", x, x)));
    lean_assert(!closed(pi("x", p, y)));
    lean_assert(closed(pi("x", p, f(f(f(a))))));
    lean_assert(closed(lambda("y", p, lambda("x", p, y))));
    lean_assert(closed(lambda("y", p, app(lambda("x", p, y), var(0)))));
    expr r = lambda("y", p, app(lambda("x", p, y), var(0)));
    lean_assert(closed(r));
    lean_assert(closed(r));
    r = lambda("y", p, app(lambda("x", p, y), var(1)));
    lean_assert(!closed(r));
    r = lambda("y", p, app(lambda("x", p, var(0)), var(1)));
    lean_assert(!closed(r));
    lean_assert(closed(lambda("z", p, r)));
}

void tst9() {
    expr r = mk_dag(20, true);
    lean_assert(closed(r));
    r = mk_dag(20, false);
    lean_assert(!closed(r));
}

void tst10() {
    expr f = constant("f");
    expr r = mk_big(f, 16, 0);
    for (unsigned i = 0; i < 1000; i++) {
        lean_assert(closed(r));
    }
}

/**
   \brief Substitute s with t in e.

   \pre s and t must be closed expressions (i.e., no free variables)
*/
inline expr substitute(expr const & s, expr const & t, expr const & e) {
    return instantiate(t, abstract(s, e));
}

void tst11() {
    expr f = constant("f");
    expr a = constant("a");
    expr b = constant("b");
    expr x = var(0);
    expr y = var(1);
    std::cout << instantiate(f(a), lambda("x", prop(), f(f(y, b), f(x, y)))) << "\n";
    lean_assert(instantiate(f(a), lambda("x", prop(), f(f(y, b), f(x, y)))) ==
                lambda("x", prop(), f(f(f(a), b), f(x, f(a)))));
    std::cout << abstract(constant("a"), lambda("x", prop(), f(a, lambda("y", prop(), f(b, a))))) << "\n";
    lean_assert(abstract(constant("a"), lambda("x", prop(), f(a, lambda("y", prop(), f(b, a))))) ==
                lambda("x", prop(), f(var(1), lambda("y", prop(), f(b, var(2))))));
    std::cout << abstract_p(constant("a"), lambda("x", prop(), f(a, lambda("y", prop(), f(b, a))))) << "\n";
    lean_assert(abstract_p(constant("a"), lambda("x", prop(), f(a, lambda("y", prop(), f(b, a))))) ==
                lambda("x", prop(), f(a, lambda("y", prop(), f(b, a)))));
    std::cout << abstract_p(a, lambda("x", prop(), f(a, lambda("y", prop(), f(b, a))))) << "\n";
    lean_assert(abstract_p(a, lambda("x", prop(), f(a, lambda("y", prop(), f(b, a))))) ==
                lambda("x", prop(), f(var(1), lambda("y", prop(), f(b, var(2))))));

    lean_assert(substitute(f(a), b, f(f(f(a)))) == f(f(b)));
}

void tst12() {
    expr f = constant("f");
    expr a = constant("a");
    expr x = var(0);
    expr F = pi("y", prop(), lambda("x", prop(), f(f(f(x,a),numeral(10)),x)));
    expr G = deep_copy(F);
    lean_assert(F == G);
    lean_assert(!eqp(F, G));
    lean_assert(count(F) == count(G));
}

void tst13() {
    expr f  = constant("f");
    expr v  = var(0);
    expr a1 = max_sharing(f(v,v));
    expr a2 = max_sharing(f(v,v));
    lean_assert(!eqp(a1, a2));
    lean_assert(a1 == a2);
    max_sharing_fn M;
    lean_assert(eqp(M(f(v,v)), M(f(v,v))));
    lean_assert(eqp(M(a1), M(a2)));
}

int main() {
    continue_on_violation(true);
    std::cout << "sizeof(expr):      " << sizeof(expr) << "\n";
    std::cout << "sizeof(expr_app):  " << sizeof(expr_app) << "\n";
    std::cout << "sizeof(expr_cell): " << sizeof(expr_cell) << "\n";
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
    std::cout << "done" << "\n";
    return has_violations() ? 1 : 0;
}
