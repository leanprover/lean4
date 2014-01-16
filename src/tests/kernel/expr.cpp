/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include <algorithm>
#include <utility>
#include <vector>
#include "util/test.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/max_sharing.h"
#include "library/printer.h"
#include "library/bin_op.h"
#include "library/arith/arith.h"
using namespace lean;

static void check_serializer(expr const & e) {
    std::ostringstream out;
    serializer s(out);
    s << e << e;
    std::cout << "OUT size: " << out.str().size() << "\n";
    std::istringstream in(out.str());
    deserializer d(in);
    expr n1, n2;
    d >> n1 >> n2;
    lean_assert(e == n1);
    lean_assert(e == n2);
    lean_assert(is_eqp(n1, n2));
}

static void tst1() {
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

static expr mk_dag(unsigned depth, bool _closed = false) {
    expr f = Const("f");
    expr a = _closed ? Const("a") : Var(0);
    while (depth > 0) {
        depth--;
        a = f(a, a);
    }
    return a;
}

// This is the fastest depth implementation in this file.
static unsigned depth2(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type:
    case expr_kind::Value: case expr_kind::MetaVar:
        return 1;
    case expr_kind::App:
        return
            std::accumulate(begin_args(e), end_args(e), 0,
                            [](unsigned m, expr const & arg){ return std::max(depth2(arg), m); })
            + 1;
    case expr_kind::HEq:
        return std::max(depth2(heq_lhs(e)), depth2(heq_rhs(e))) + 1;
    case expr_kind::Lambda: case expr_kind::Pi:
        return std::max(depth2(abst_domain(e)), depth2(abst_body(e))) + 1;
    case expr_kind::Let:
        return std::max(depth2(let_value(e)), depth2(let_body(e))) + 1;
    }
    return 0;
}

static void tst2() {
    expr r1 = mk_dag(20);
    expr r2 = mk_dag(20);
    lean_assert(r1 == r2);
    std::cout << depth2(r1) << "\n";
    lean_assert(depth2(r1) == 21);
}

static expr mk_big(expr f, unsigned depth, unsigned val) {
    if (depth == 1)
        return Const(name(name("foo"), val));
    else
        return f(mk_big(f, depth - 1, val << 1), mk_big(f, depth - 1, (val << 1) + 1));
}

static void tst3() {
    expr f = Const("f");
    expr r1 = mk_big(f, 16, 0);
    expr r2 = mk_big(f, 16, 0);
    lean_assert(r1 == r2);
    check_serializer(r1);
}

static void tst4() {
    expr f = Const("f");
    expr a = Var(0);
    for (unsigned i = 0; i < 10000; i++) {
        a = f(a);
    }
}

static expr mk_redundant_dag(expr f, unsigned depth) {
    if (depth == 0)
        return Var(0);
    else
        return f(mk_redundant_dag(f, depth - 1), mk_redundant_dag(f, depth - 1));
}

static unsigned count_core(expr const & a, expr_set & s) {
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
    case expr_kind::HEq:
        return count_core(heq_lhs(a), s) + count_core(heq_rhs(a), s) + 1;
    case expr_kind::Lambda: case expr_kind::Pi:
        return count_core(abst_domain(a), s) + count_core(abst_body(a), s) + 1;
    case expr_kind::Let:
        return count_core(let_value(a), s) + count_core(let_body(a), s) + 1;
    }
    return 0;
}

static unsigned count(expr const & a) {
    expr_set s;
    return count_core(a, s);
}

static void tst5() {
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

static void tst6() {
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

static void tst7() {
    expr f  = Const("f");
    expr v  = Var(0);
    expr a1 = max_sharing(f(v, v));
    expr a2 = max_sharing(f(v, v));
    lean_assert(!is_eqp(a1, a2));
    expr b  = max_sharing(f(a1, a2));
    lean_assert(is_eqp(arg(b, 1), arg(b, 2)));
}

static void tst8() {
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

static void tst9() {
    expr r = mk_dag(20, true);
    lean_assert(closed(r));
    r = mk_dag(20, false);
    lean_assert(!closed(r));
}

static void tst10() {
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
static expr substitute(expr const & e, expr const & s, expr const & t) {
    check_serializer(e);
    return instantiate(abstract(e, s), t);
}

static void tst11() {
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

static void tst12() {
    expr f  = Const("f");
    expr v  = Var(0);
    expr a1 = max_sharing(f(v, v));
    expr a2 = max_sharing(f(v, v));
    lean_assert(!is_eqp(a1, a2));
    lean_assert(a1 == a2);
    max_sharing_fn M;
    lean_assert(is_eqp(M(f(v, v)), M(f(v, v))));
    lean_assert(is_eqp(M(a1), M(a2)));
}

static void tst13() {
    expr t0 = Type();
    expr t1 = Type(level()+1);
    check_serializer(t0);
    check_serializer(t1);
    lean_assert(ty_level(t1) == level()+1);
    lean_assert(t0 != t1);
    std::cout << t0 << " " << t1 << "\n";
}

static void tst14() {
    expr t = HEq(Const("a"), Const("b"));
    check_serializer(t);
    std::cout << t << "\n";
    expr l = mk_let("a", none_expr(), Const("b"), Var(0));
    check_serializer(l);
    std::cout << l << "\n";
    lean_assert(closed(l));
}

static void tst15() {
    expr f = Const("f");
    expr x = Var(0);
    expr a = Const("a");
    expr m = mk_metavar("m");
    check_serializer(m);
    lean_assert(has_metavar(m));
    lean_assert(has_metavar(f(m)));
    lean_assert(!has_metavar(f(a)));
    lean_assert(!has_metavar(f(x)));
    lean_assert(!has_metavar(Pi({a, Type()}, a)));
    lean_assert(!has_metavar(Type()));
    lean_assert(!has_metavar(Fun({a, Type()}, a)));
    lean_assert(has_metavar(Pi({a, Type()}, m)));
    lean_assert(has_metavar(Pi({a, m}, a)));
    lean_assert(has_metavar(Fun({a, Type()}, m)));
    lean_assert(has_metavar(Fun({a, m}, a)));
    lean_assert(!has_metavar(Let({a, Type()}, a)));
    lean_assert(!has_metavar(mk_let(name("a"), Type(), f(x), f(f(x)))));
    lean_assert(has_metavar(mk_let(name("a"), m, f(x), f(f(x)))));
    lean_assert(has_metavar(mk_let(name("a"), Type(), f(m), f(f(x)))));
    lean_assert(has_metavar(mk_let(name("a"), Type(), f(x), f(f(m)))));
    lean_assert(has_metavar(f(a, a, m)));
    lean_assert(has_metavar(f(a, m, a, a)));
    lean_assert(!has_metavar(f(a, a, a, a)));
    lean_assert(!has_metavar(HEq(a, f(a))));
    lean_assert(has_metavar(HEq(m, f(a))));
    lean_assert(has_metavar(HEq(a, f(m))));
}

static void check_copy(expr const & e) {
    expr c = copy(e);
    lean_assert(!is_eqp(e, c));
    lean_assert(e == c);
    check_serializer(e);
}

static void tst16() {
    expr f = Const("f");
    expr a = Const("a");
    check_copy(iVal(10));
    check_copy(f(a));
    check_copy(HEq(f(a), a));
    check_copy(mk_metavar("M"));
    check_copy(mk_lambda("x", a, Var(0)));
    check_copy(mk_pi("x", a, Var(0)));
    check_copy(mk_let("x", none_expr(), a, Var(0)));
}

static void tst17() {
    lean_assert(is_true(True));
    lean_assert(is_false(False));
    lean_assert(!is_true(Const("a")));
    lean_assert(!is_false(Const("a")));
    check_serializer(True);
    check_serializer(False);
}

static void tst18() {
    expr f = Const("f");
    expr a = Const("a");
    lean_assert_eq(mk_bin_rop(f, a, 0, nullptr), a);
    expr b = Const("b");
    lean_assert_eq(mk_bin_rop(f, a, 1, &b), b);
    expr a1 = Const("a1"); expr a2 = Const("a2"); expr a3 = Const("a3");
    expr ar[] = { a1, a2, a3 };
    lean_assert_eq(mk_bin_rop(f, a, 3, ar), f(a1, f(a2, a3)));
    lean_assert_eq(mk_bin_rop(f, a, {a1, a2, a3}), f(a1, f(a2, a3)));
    lean_assert_eq(mk_bin_lop(f, a, 0, nullptr), a);
    lean_assert_eq(mk_bin_lop(f, a, 1, &b), b);
    lean_assert_eq(mk_bin_lop(f, a, 3, ar), f(f(a1, a2), a3));
    lean_assert_eq(mk_bin_lop(f, a, {a1, a2, a3}), f(f(a1, a2), a3));
}

static void tst19() {
    expr T1 = Const("T1");
    expr T2 = Const("T2");
    lean_assert(extend(extend(context(), "a", T1), "b", T2) == context({{"a", T1}, {"b", T2}}));
    lean_assert(extend(extend(context(), "a", T1), "b", T2) == context({{"b", T1}, {"a", T2}})); // names don't matter
    lean_assert(extend(extend(context(), "a", T2), "b", T2) != context({{"a", T1}, {"b", T2}}));
}

static void tst20() {
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr c = Const("c");
    buffer<expr> args;
    args.push_back(f);
    for (unsigned i = 0; i < 200; i++) {
        args.push_back(a);
        args.push_back(b);
    }
    args.push_back(c);
    expr t = mk_app(args);
    check_serializer(t);
}

int main() {
    save_stack_info();
    lean_assert(sizeof(expr) == sizeof(optional<expr>));
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
    tst20();
    std::cout << "sizeof(expr):            " << sizeof(expr) << "\n";
    std::cout << "sizeof(expr_app):        " << sizeof(expr_app) << "\n";
    std::cout << "sizeof(expr_cell):       " << sizeof(expr_cell) << "\n";
    std::cout << "sizeof(optional<expr>):  " << sizeof(optional<expr>) << "\n";
    std::cout << "sizeof(optional<sexpr>): " << sizeof(optional<sexpr>) << "\n";
    std::cout << "done" << "\n";
    return has_violations() ? 1 : 0;
}
