/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "expr.h"
#include "expr_max_shared.h"
#include "expr_set.h"
#include "test.h"
#include <algorithm>
using namespace lean;

void tst1() {
    expr a;
    a = numeral(mpz(10));
    expr f;
    f = var(0);
    expr fa = app({f, a});
    std::cout << fa << "\n";
    std::cout << app({fa, a}) << "\n";
    lean_assert(eqp(get_arg(fa, 0), f));
    lean_assert(eqp(get_arg(fa, 1), a));
    lean_assert(!eqp(fa, app({f, a})));
    lean_assert(app({fa, a}) == app({f, a, a}));
    std::cout << app({fa, fa, fa}) << "\n";
    std::cout << lambda(name("x"), prop(), var(0)) << "\n";
}

expr mk_dag(unsigned depth) {
    expr f = constant(name("f"));
    expr a = var(0);
    while (depth > 0) {
        depth--;
        a = app({f, a, a});
    }
    return a;
}

unsigned depth1(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral:
        return 1;
    case expr_kind::App: {
        unsigned m = 0;
        for (expr const & a : app_args(e))
            m = std::max(m, depth1(a));
        return m + 1;
    }
    case expr_kind::Lambda: case expr_kind::Pi:
        return std::max(depth1(get_abs_type(e)), depth1(get_abs_expr(e))) + 1;
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
        return std::max(depth2(get_abs_type(e)), depth2(get_abs_expr(e))) + 1;
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
            unsigned num = get_num_args(e);
            for (unsigned i = 0; i < num; i++)
                todo.push_back(std::make_pair(&get_arg(e, i), c));
            break;
        }
        case expr_kind::Lambda: case expr_kind::Pi:
            todo.push_back(std::make_pair(&get_abs_type(e), c));
            todo.push_back(std::make_pair(&get_abs_expr(e), c));
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
        return var(val);
    else
        return app({f, mk_big(f, depth - 1, val << 1), mk_big(f, depth - 1, (val << 1) + 1)});
}

void tst3() {
    expr f = constant(name("f"));
    expr r1 = mk_big(f, 18, 0);
    expr r2 = mk_big(f, 18, 0);
    lean_verify(r1 == r2);
}

void tst4() {
    expr f = constant(name("f"));
    expr a = var(0);
    for (unsigned i = 0; i < 10000; i++) {
        a = app({f, a});
    }
}

expr mk_redundant_dag(expr f, unsigned depth) {
    if (depth == 0)
        return var(0);
    else
        return app({f, mk_redundant_dag(f, depth - 1), mk_redundant_dag(f, depth - 1)});
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
        return count_core(get_abs_type(a), s) + count_core(get_abs_expr(a), s) + 1;
    }
    return 0;
}

unsigned count(expr const & a) {
    expr_set s;
    return count_core(a, s);
}

void tst5() {
    expr f  = constant(name("f"));
    expr r1 = mk_redundant_dag(f, 1);
    expr r2 = max_shared(r1);
    std::cout << "r1: " << r1 << "\n";
    std::cout << "r2: " << r1 << "\n";
    std::cout << "count(r1): " << count(r1) << "\n";
    std::cout << "count(r2): " << count(r2) << "\n";
    lean_assert(r1 == r2);
}

int main() {
    // continue_on_violation(true);
    std::cout << "sizeof(expr):     " << sizeof(expr) << "\n";
    std::cout << "sizeof(expr_app): " << sizeof(expr_app) << "\n";
    // tst1();
    // tst2();
    // tst3();
    // tst4();
    tst5();
    std::cout << "done" << "\n";
    return has_violations() ? 1 : 0;
}
