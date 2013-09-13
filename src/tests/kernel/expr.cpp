/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include <algorithm>
#include "util/test.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/max_sharing.h"
#include "library/deep_copy.h"
#include "library/printer.h"
#include "library/arith/arithlibs.h"
using namespace lean;

void tst1() {
    expr a;
    a = Const("a");
    expr f;
    f = Var(0);
    expr fa = f(a);
    expr ty = Type();
    std::cout << fa << "\n";
    std::cout << fa(a) << "\n";
    lean_assert(is_eqp(arg(fa, 0), f));
    lean_assert(is_eqp(arg(fa, 1), a));
    lean_assert(!is_eqp(fa, f(a)));
    lean_assert(fa(a) == f(a, a));
    std::cout << fa(fa, fa) << "\n";
    std::cout << mk_lambda("x", ty, Var(0)) << "\n";
    lean_assert(f(a)(a) == f(a, a));
    lean_assert(f(a(a)) != f(a, a));
    lean_assert(mk_lambda("x", ty, Var(0)) == mk_lambda("y", ty, Var(0)));
    std::cout << mk_pi("x", ty, Var(0)) << "\n";
}

expr mk_dag(unsigned depth, bool _closed = false) {
    expr f = Const("f");
    expr a = _closed ? Const("a") : Var(0);
    while (depth > 0) {
        depth--;
        a = f(a, a);
    }
    return a;
}

unsigned depth1(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
        return 1;
    case expr_kind::App: {
        unsigned m = 0;
        for (expr const & a : args(e))
            m = std::max(m, depth1(a));
        return m + 1;
    }
    case expr_kind::Eq:
        return std::max(depth1(eq_lhs(e)), depth1(eq_rhs(e))) + 1;
    case expr_kind::Lambda: case expr_kind::Pi:
        return std::max(depth1(abst_domain(e)), depth1(abst_body(e))) + 1;
    case expr_kind::Let:
        return std::max(depth1(let_value(e)), depth1(let_body(e))) + 1;
    }
    return 0;
}

// This is the fastest depth implementation in this file.
unsigned depth2(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
        return 1;
    case expr_kind::App:
        return
            std::accumulate(begin_args(e), end_args(e), 0,
                            [](unsigned m, expr const & arg){ return std::max(depth2(arg), m); })
            + 1;
    case expr_kind::Eq:
        return std::max(depth2(eq_lhs(e)), depth2(eq_rhs(e))) + 1;
    case expr_kind::Lambda: case expr_kind::Pi:
        return std::max(depth2(abst_domain(e)), depth2(abst_body(e))) + 1;
    case expr_kind::Let:
        return std::max(depth2(let_value(e)), depth2(let_body(e))) + 1;
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
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
            m = std::max(c, m);
            break;
        case expr_kind::App: {
            unsigned num = num_args(e);
            for (unsigned i = 0; i < num; i++)
                todo.push_back(std::make_pair(&arg(e, i), c));
            break;
        }
        case expr_kind::Eq:
            todo.push_back(std::make_pair(&eq_lhs(e), c));
            todo.push_back(std::make_pair(&eq_rhs(e), c));
            break;
        case expr_kind::Lambda: case expr_kind::Pi:
            todo.push_back(std::make_pair(&abst_domain(e), c));
            todo.push_back(std::make_pair(&abst_body(e), c));
            break;
        case expr_kind::Let:
            todo.push_back(std::make_pair(&let_value(e), c));
            todo.push_back(std::make_pair(&let_body(e), c));
            break;
        }
    }
    return m;
}

void tst2() {
    expr r1 = mk_dag(20);
    expr r2 = mk_dag(20);
    lean_assert(r1 == r2);
    std::cout << depth2(r1) << "\n";
    lean_assert(depth2(r1) == 21);
}

expr mk_big(expr f, unsigned depth, unsigned val) {
    if (depth == 1)
        return Const(name(val));
    else
        return f(mk_big(f, depth - 1, val << 1), mk_big(f, depth - 1, (val << 1) + 1));
}

void tst3() {
    expr f = Const("f");
    expr r1 = mk_big(f, 18, 0);
    expr r2 = mk_big(f, 18, 0);
    lean_assert(r1 == r2);
}

void tst4() {
    expr f = Const("f");
    expr a = Var(0);
    for (unsigned i = 0; i < 10000; i++) {
        a = f(a);
    }
}

expr mk_redundant_dag(expr f, unsigned depth) {
    if (depth == 0)
        return Var(0);
    else
        return f(mk_redundant_dag(f, depth - 1), mk_redundant_dag(f, depth - 1));
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

void tst5() {
    expr f  = Const("f");
    {
        expr r1 = mk_redundant_dag(f, 5);
        expr r2 = max_sharing(r1);
        std::cout << "count(r1): " << count(r1) << "\n";
        std::cout << "count(r2): " << count(r2) << "\n";
        std::cout << "r1 = " << std::endl;
        std::cout << r1 << std::endl;
        std::cout << "r2 = " << std::endl;
        std::cout << r2 << std::endl;
        lean_assert(r1 == r2);
    }
    {
        expr r1 = mk_redundant_dag(f, 16);
        expr r2 = max_sharing(r1);
        lean_assert(r1 == r2);
    }
}

void tst6() {
    expr f = Const("f");
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
    expr f  = Const("f");
    expr v  = Var(0);
    expr a1 = max_sharing(f(v,v));
    expr a2 = max_sharing(f(v,v));
    lean_assert(!is_eqp(a1, a2));
    expr b  = max_sharing(f(a1, a2));
    lean_assert(is_eqp(arg(b, 1), arg(b, 2)));
}

void tst8() {
    expr f = Const("f");
    expr x = Var(0);
    expr a = Const("a");
    expr n = Const("n");
    expr p = Type();
    expr y = Var(1);
    lean_assert(closed(a));
    lean_assert(!closed(x));
    lean_assert(closed(f));
    lean_assert(!closed(f(x)));
    lean_assert(closed(mk_lambda("x", p, x)));
    lean_assert(!closed(mk_lambda("x", x, x)));
    lean_assert(!closed(mk_lambda("x", p, y)));
    lean_assert(closed(f(f(f(a)))));
    lean_assert(closed(mk_lambda("x", p, f(f(f(a))))));
    lean_assert(closed(mk_pi("x", p, x)));
    lean_assert(!closed(mk_pi("x", x, x)));
    lean_assert(!closed(mk_pi("x", p, y)));
    lean_assert(closed(mk_pi("x", p, f(f(f(a))))));
    lean_assert(closed(mk_lambda("y", p, mk_lambda("x", p, y))));
    lean_assert(closed(mk_lambda("y", p, mk_app({mk_lambda("x", p, y), Var(0)}))));
    expr r = mk_lambda("y", p, mk_app({mk_lambda("x", p, y), Var(0)}));
    lean_assert(closed(r));
    lean_assert(closed(r));
    r = mk_lambda("y", p, mk_app({mk_lambda("x", p, y), Var(1)}));
    lean_assert(!closed(r));
    r = mk_lambda("y", p, mk_app({mk_lambda("x", p, Var(0)), Var(1)}));
    lean_assert(!closed(r));
    lean_assert(closed(mk_lambda("z", p, r)));
}

void tst9() {
    expr r = mk_dag(20, true);
    lean_assert(closed(r));
    r = mk_dag(20, false);
    lean_assert(!closed(r));
}

void tst10() {
    expr f = Const("f");
    expr r = mk_big(f, 16, 0);
    for (unsigned i = 0; i < 1000; i++) {
        lean_assert(closed(r));
    }
}

/**
   \brief Substitute s with t in e.

   \pre s and t must be closed expressions (i.e., no free variables)
*/
inline expr substitute(expr const & e, expr const & s, expr const & t) {
    return instantiate(abstract(e, s), t);
}

void tst11() {
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr x = Var(0);
    expr y = Var(1);
    expr t = Type();
    std::cout << instantiate(mk_lambda("x", t, f(f(y, b), f(x, y))), f(a)) << "\n";
    lean_assert(instantiate(mk_lambda("x", t, f(f(y, b), f(x, y))), f(a)) ==
                mk_lambda("x", t, f(f(f(a), b), f(x, f(a)))));
    std::cout << abstract(mk_lambda("x", t, f(a, mk_lambda("y", t, f(b, a)))), Const("a")) << "\n";
    lean_assert(abstract(mk_lambda("x", t, f(a, mk_lambda("y", t, f(b, a)))), Const("a")) ==
                mk_lambda("x", t, f(Var(1), mk_lambda("y", t, f(b, Var(2))))));
    std::cout << abstract_p(mk_lambda("x", t, f(a, mk_lambda("y", t, f(b, a)))), Const("a")) << "\n";
    lean_assert(abstract_p(mk_lambda("x", t, f(a, mk_lambda("y", t, f(b, a)))), Const("a")) ==
                mk_lambda("x", t, f(a, mk_lambda("y", t, f(b, a)))));
    std::cout << abstract_p(mk_lambda("x", t, f(a, mk_lambda("y", t, f(b, a)))), a) << "\n";
    lean_assert(abstract_p(mk_lambda("x", t, f(a, mk_lambda("y", t, f(b, a)))), a) ==
                mk_lambda("x", t, f(Var(1), mk_lambda("y", t, f(b, Var(2))))));

    lean_assert(substitute(f(f(f(a))), f(a), b) == f(f(b)));
}

void tst12() {
    expr f = Const("f");
    expr a = Const("a");
    expr x = Var(0);
    expr t = Type();
    expr F = mk_pi("y", t, mk_lambda("x", t, f(f(f(x,a),Const("10")),x)));
    expr G = deep_copy(F);
    lean_assert(F == G);
    lean_assert(!is_eqp(F, G));
    lean_assert(count(F) == count(G));
}

void tst13() {
    expr f  = Const("f");
    expr v  = Var(0);
    expr a1 = max_sharing(f(v,v));
    expr a2 = max_sharing(f(v,v));
    lean_assert(!is_eqp(a1, a2));
    lean_assert(a1 == a2);
    max_sharing_fn M;
    lean_assert(is_eqp(M(f(v,v)), M(f(v,v))));
    lean_assert(is_eqp(M(a1), M(a2)));
}

void tst14() {
    expr t0 = Type();
    expr t1 = Type(level()+1);
    lean_assert(ty_level(t1) == level()+1);
    lean_assert(t0 != t1);
    std::cout << t0 << " " << t1 << "\n";
}

void tst15() {
    expr t = Eq(Const("a"), Const("b"));
    std::cout << t << "\n";
    expr l = mk_let("a", expr(), Const("b"), Var(0));
    std::cout << l << "\n";
    lean_assert(closed(l));
}

int main() {
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
    tst14();
    tst15();
    std::cout << "done" << "\n";
    return has_violations() ? 1 : 0;
}
