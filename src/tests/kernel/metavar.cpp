/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <algorithm>
#include <vector>
#include <utility>
#include "util/test.h"
#include "kernel/metavar.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "kernel/normalizer.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "library/printer.h"
#include "library/placeholder.h"
using namespace lean;

class unification_constraints_dbg : public unification_constraints {
    typedef std::tuple<context, expr, expr> constraint;
    typedef std::vector<constraint>         constraints;
    constraints m_eqs;
    constraints m_type_of_eqs;
public:
    unification_constraints_dbg() {}
    virtual ~unification_constraints_dbg() {}
    virtual void add(context const & ctx, expr const & lhs, expr const & rhs) { m_eqs.push_back(constraint(ctx, lhs, rhs)); }
    virtual void add_type_of(context const & ctx, expr const & n, expr const & t) { m_type_of_eqs.push_back(constraint(ctx, n, t)); }
    constraints const & eqs() const { return m_eqs; }
    constraints const & type_of_eqs() const { return m_type_of_eqs; }
    friend std::ostream & operator<<(std::ostream & out, unification_constraints_dbg const & uc) {
        for (auto c : uc.m_eqs)
            std::cout << std::get<0>(c) << " |- " << std::get<1>(c) << " == " << std::get<2>(c) << "\n";
        for (auto c : uc.m_type_of_eqs)
            std::cout << std::get<0>(c) << " |- " << std::get<1>(c) << " : " << std::get<2>(c) << "\n";
        return out;
    }
};

std::ostream & operator<<(std::ostream & out, substitution const & env) {
    bool first = true;
    env.for_each([&](name const & n, expr const & v) {
            if (first) first = false; else out << "\n";
            out << "?M" << n << " <- " << v;
        });
    return out;
}

static void tst1() {
    substitution          subst;
    metavar_generator     gen;
    expr m1 = gen.mk();
    lean_assert(!subst.is_assigned(m1));
    expr t1 = metavar_type(m1);
    lean_assert(is_metavar(t1));
    lean_assert(is_eqp(metavar_type(m1), t1));
    lean_assert(is_eqp(metavar_type(m1), t1));
    lean_assert(!subst.is_assigned(m1));
    expr m2 = gen.mk();
    lean_assert(!subst.is_assigned(m1));
    expr t2 = metavar_type(m2);
    lean_assert(is_metavar(m2));
    lean_assert(!is_eqp(t1, t2));
    lean_assert(t1 != t2);
    expr f = Const("f");
    expr a = Const("a");
    subst.assign(m1, f(a));
    lean_assert(subst.is_assigned(m1));
    lean_assert(!subst.is_assigned(m2));
    lean_assert(subst.get_subst(m1) == f(a));
}

static void tst2() {
    substitution subst;
    metavar_generator gen;
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr a = Const("a");
    expr m1 = gen.mk();
    expr m2 = gen.mk();
    // move m1 to a different context, and store new metavariable + context in m11
    std::cout << "---------------------\n";
    expr m11 = add_inst(m1, 0, f(a, m2));
    std::cout << m11 << "\n";
    subst.assign(m1, f(Var(0)));
    std::cout << instantiate_metavars(m11, subst) << "\n";
    subst.assign(m2, g(a, Var(1)));
    std::cout << instantiate_metavars(h(m11), subst) << "\n";
    lean_assert(instantiate_metavars(h(m11), subst) == h(f(f(a, g(a, Var(1))))));
}

static void tst3() {
    substitution subst;
    metavar_generator gen;
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr a = Const("a");
    expr x = Const("x");
    expr T = Const("T");
    expr m1 = gen.mk();
    expr F = Fun({x, T}, f(m1, x));
    subst.assign(m1, h(Var(0), Var(2)));
    std::cout << instantiate(abst_body(F), g(a)) << "\n";
    std::cout << instantiate_metavars(instantiate(abst_body(F), g(a)), subst) << "\n";
    lean_assert(instantiate_metavars(instantiate(abst_body(F), g(a)), subst) == f(h(g(a), Var(1)), g(a)));
    std::cout << instantiate(instantiate_metavars(abst_body(F), subst), g(a)) << "\n";
    lean_assert(instantiate(instantiate_metavars(abst_body(F), subst), g(a)) ==
                instantiate_metavars(instantiate(abst_body(F), g(a)), subst));
}

static void tst4() {
    substitution subst;
    metavar_generator gen;
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr a = Const("a");
    expr m1 = gen.mk();
    expr F = f(m1, Var(2));
    subst.assign(m1, h(Var(1)));
    std::cout << instantiate(F, {g(Var(0)), h(a)}) << "\n";
    std::cout << instantiate_metavars(instantiate(F, {g(Var(0)), h(a)}), subst) << "\n";
}

static void tst5() {
    return;
}

static void tst6() {
    expr N  = Const("N");
    expr f  = Const("f");
    expr x  = Const("x");
    expr y  = Const("y");
    expr a  = Const("a");
    expr g  = Const("g");
    expr h  = Const("h");
    substitution subst;
    metavar_generator gen;
    expr m1 = gen.mk();
    expr m2 = gen.mk();
    expr t = f(Var(0), Fun({x, N}, f(Var(1), x, Fun({y, N}, f(Var(2), x, y)))));
    expr r = instantiate(t, g(m1, m2));
    std::cout << r << std::endl;
    subst.assign(m2, Var(2));
    r = instantiate_metavars(r, subst);
    std::cout << r << std::endl;
    subst.assign(m1, h(Var(3)));
    r = instantiate_metavars(r, subst);
    std::cout << r << std::endl;
    lean_assert(r == f(g(h(Var(3)), Var(2)), Fun({x, N}, f(g(h(Var(4)), Var(3)), x, Fun({y, N}, f(g(h(Var(5)), Var(4)), x, y))))));
}

static void tst7() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    substitution subst;
    metavar_generator gen;
    expr m1 = gen.mk();
    expr t  = f(m1, Var(0));
    expr r = instantiate(t, a);
    subst.assign(m1, g(Var(0)));
    r = instantiate_metavars(r, subst);
    std::cout << r << std::endl;
    lean_assert(r == f(g(a), a));
}

static void tst8() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    substitution subst;
    metavar_generator gen;
    expr m1 = gen.mk();
    expr t  = f(m1, Var(0), Var(2));
    expr r = instantiate(t, a);
    subst.assign(m1, g(Var(0), Var(1)));
    r = instantiate_metavars(r, subst);
    std::cout << r << std::endl;
    lean_assert(r == f(g(a, Var(0)), a, Var(1)));
}

static void tst9() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    substitution subst;
    metavar_generator gen;
    expr m1 = gen.mk();
    expr t  = f(m1, Var(1), Var(2));
    expr r  = lift_free_vars(t, 1, 2);
    std::cout << r << std::endl;
    r = instantiate(r, a);
    std::cout << r << std::endl;
    subst.assign(m1, g(Var(0), Var(1)));
    r = instantiate_metavars(r, subst);
    std::cout << r << std::endl;
    lean_assert(r == f(g(a, Var(2)), Var(2), Var(3)));
}

static void tst10() {
    expr N  = Const("N");
    expr f  = Const("f");
    expr x  = Const("x");
    expr y  = Const("y");
    expr a  = Const("a");
    expr g  = Const("g");
    expr h  = Const("h");
    substitution subst;
    metavar_generator gen;
    expr m1 = gen.mk();
    expr m2 = gen.mk();
    expr t = f(Var(0), Fun({x, N}, f(Var(1), Var(2), x, Fun({y, N}, f(Var(2), x, y)))));
    expr r = instantiate(t, g(m1));
    std::cout << r << std::endl;
    r = instantiate(r, h(m2));
    std::cout << r << std::endl;
    subst.assign(m1, f(Var(0)));
    subst.assign(m2, Var(2));
    r = instantiate_metavars(r, subst);
    std::cout << r << std::endl;
    lean_assert(r == f(g(f(h(Var(2)))), Fun({x, N}, f(g(f(h(Var(3)))), h(Var(3)), x, Fun({y, N}, f(g(f(h(Var(4)))), x, y))))));
}

static void tst11() {
    substitution subst;
    unsigned t1 = subst.get_timestamp();
    metavar_generator gen;
    expr m = gen.mk();
    unsigned t2 = subst.get_timestamp();
    lean_assert(t2 == t1);
    lean_assert(!subst.is_assigned(m));
    lean_assert(subst.get_timestamp() == t2);
    subst.assign(m, Const("a"));
    lean_assert(subst.get_timestamp() > t2);
}

static void tst12() {
    substitution subst;
    metavar_generator gen;
    expr m = gen.mk();
    expr f = Const("f");
    std::cout << instantiate(f(m), {Var(0), Var(1)}) << "\n";
    std::cout << instantiate(f(m), {Var(1), Var(0)}) << "\n";
}

static void tst13() {
    environment env;
    substitution subst;
    metavar_generator gen;
    expr m = gen.mk();
    env.add_var("N", Type());
    expr N = Const("N");
    env.add_var("f", N >> N);
    expr f = Const("f");
    env.add_var("a", N);
    expr a = Const("a");
    expr x = Const("x");
    expr F = Fun({x, N}, f(m))(a);
    normalizer norm(env);
    std::cout << norm(F) << "\n";
    subst.assign(m, Var(0));
    std::cout << norm(instantiate_metavars(F, subst)) << "\n";
    lean_assert(norm(instantiate_metavars(F, subst)) ==
                instantiate_metavars(norm(F), subst));
}

static void tst14() {
    environment env;
    substitution subst;
    metavar_generator gen;
    expr m1 = gen.mk();
    expr m2 = gen.mk();
    expr N = Const("N");
    expr f = Const("f");
    expr h = Const("h");
    expr a = Const("a");
    expr b = Const("b");
    expr x = Const("x");
    expr y = Const("y");
    env.add_var("h", Pi({N, Type()}, N >> (N >> N)));
    expr F1 = Fun({{N, Type()}, {a, N}, {f, N >> N}},
                  (Fun({{x, N}, {y, N}}, Eq(f(m1), y)))(a));
    substitution subst2 = subst;
    subst2.assign(m1, h(Var(4), Var(1), Var(3)));
    normalizer norm(env);
    env.add_var("M", Type());
    expr M = Const("M");
    std::cout << norm(F1) << "\n";
    std::cout << instantiate_metavars(norm(F1), subst2) << "\n";
    std::cout << instantiate_metavars(F1, subst2) << "\n";
    std::cout << norm(instantiate_metavars(F1, subst2)) << "\n";
    lean_assert(instantiate_metavars(norm(F1), subst2) ==
                norm(instantiate_metavars(F1, subst2)));
    expr F2 = (Fun({{N, Type()}, {f, N >> N}, {a, N}, {b, N}},
                   (Fun({{x, N}, {y, N}}, Eq(f(m1), y)))(a, m2)))(M);
    std::cout << norm(F2) << "\n";
    expr F3 = (Fun({{N, Type()}, {f, N >> N}, {a, N}, {b, N}},
                   (Fun({{x, N}, {y, N}}, Eq(f(m1), y)))(b, m2)))(M);
    std::cout << norm(F3) << "\n";
}

static void tst15() {
    environment env;
    substitution subst;
    normalizer  norm(env);
    metavar_generator gen;
    expr m1 = gen.mk();
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    env.add_var("N", Type());
    env.add_var("f", Type() >> Type());
    expr F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}}, f(m1))(N, N));
    subst.assign(m1, Var(2));
    std::cout << norm(F) << "\n";
    std::cout << instantiate_metavars(norm(F), subst) << "\n";
    std::cout << norm(instantiate_metavars(F, subst)) << "\n";
    lean_assert(instantiate_metavars(norm(F), subst) ==
                norm(instantiate_metavars(F, subst)));
}

static void tst16() {
    environment env;
    substitution subst;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w", Type());
    metavar_generator gen;
    expr m1 = gen.mk();
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    env.add_var("N", Type());
    expr F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}}, m1)(N, N));
    subst.assign(m1, Var(3));
    std::cout << norm(F, ctx) << "\n";
    std::cout << instantiate_metavars(norm(F, ctx), subst) << "\n";
    std::cout << norm(instantiate_metavars(F, subst), ctx) << "\n";
}

static void tst17() {
    environment env;
    substitution subst;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w1", Type());
    ctx = extend(ctx, "w2", Type());
    ctx = extend(ctx, "w3", Type());
    ctx = extend(ctx, "w4", Type());
    metavar_generator gen;
    expr m1 = gen.mk();
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    env.add_var("N", Type());
    expr F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}}, m1)(N, N));
    substitution subst2 = subst;
    subst.assign(m1, Var(3));
    std::cout << norm(F, ctx) << "\n";
    std::cout << instantiate_metavars(norm(F, ctx), subst) << "\n";
    std::cout << norm(instantiate_metavars(F, subst), ctx) << "\n";
    F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}, {x, Type()}, {y, Type()}, {x, Type()}}, m1)(N, N, N, N, N));
    lean_assert(instantiate_metavars(norm(F, ctx), subst) ==
                norm(instantiate_metavars(F, subst), ctx));
    std::cout << "----------------------\n";
    subst2.assign(m1, Var(8));
    std::cout << norm(F, ctx) << "\n";
    std::cout << instantiate_metavars(norm(F, ctx), subst2) << "\n";
    std::cout << norm(instantiate_metavars(F, subst2), ctx) << "\n";
    lean_assert(instantiate_metavars(norm(F, ctx), subst2) ==
                norm(instantiate_metavars(F, subst2), ctx));
}

static void tst18() {
    environment env;
    substitution subst;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w1", Type());
    ctx = extend(ctx, "w2", Type());
    metavar_generator gen;
    expr m1 = gen.mk();
    expr m2 = gen.mk();
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    expr a = Const("a");
    env.add_var("N", Type());
    env.add_var("a", N);
    env.add_var("g", N >> N);
    env.add_var("h", N >> (N >> N));
    expr F = Fun({z, Type()}, Fun({{f, N >> N}, {y, Type()}}, m1)(Fun({x, N}, g(z, x, m2)), N));
    std::cout << norm(F, ctx) << "\n";
    substitution subst2 = subst;
    subst2.assign(m1, Var(1));
    subst2.assign(m2, h(Var(2), Var(1)));
    std::cout << instantiate_metavars(norm(F, ctx), subst2) << "\n";
    std::cout << instantiate_metavars(F, subst2) << "\n";
    lean_assert(instantiate_metavars(norm(F, ctx), subst2) ==
                norm(instantiate_metavars(F, subst2), ctx));
    lean_assert(instantiate_metavars(norm(F, ctx), subst2) ==
                Fun({{z, Type()}, {x, N}}, g(z, x, h(Var(2), z))));
}

static void tst19() {
    environment env;
    substitution subst;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w1", Type());
    ctx = extend(ctx, "w2", Type());
    metavar_generator gen;
    expr m1 = gen.mk();
    expr x = Const("x");
    expr y = Const("y");
    expr N = Const("N");
    expr F = Fun({{N, Type()}, {x, N}, {y, N}}, m1);
    std::cout << norm(F) << "\n";
    std::cout << norm(F, ctx) << "\n";
    lean_assert(norm(F) == F);
    lean_assert(norm(F, ctx) == F);
}

static void tst20() {
    environment env;
    substitution subst;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w1", Type());
    ctx = extend(ctx, "w2", Type());
    metavar_generator gen;
    expr m1 = gen.mk();
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    expr a = Const("a");
    expr b = Const("b");
    env.add_var("N", Type());
    env.add_var("a", N);
    env.add_var("b", N);
    expr F = Fun({{x, N}, {y, N}, {z, N}}, Fun({{x, N}, {y, N}}, m1)(a, b));
    std::cout << norm(F) << "\n";
    std::cout << norm(F, ctx) << "\n";
}

static void tst21() {
    substitution subst;
    metavar_generator gen;
    expr m1 = gen.mk();
    expr l  = add_lift(add_lift(m1, 0, 1), 1, 1);
    expr r  = add_lift(m1, 0, 2);
    std::cout << metavar_type(l) << " " << metavar_type(r) << "\n";
    lean_assert_eq(l, r);
    lean_assert_eq(add_lift(add_lift(m1, 1, 2), 3, 4),
                   add_lift(m1, 1, 6));
    lean_assert_ne(add_lift(add_lift(m1, 1, 3), 3, 4),
                   add_lift(m1, 1, 7));
}

#define _ mk_placholder()

static void tst22() {
    substitution subst;
    metavar_generator mgen;
    expr f = Const("f");
    expr x = Const("x");
    expr N = Const("N");
    expr F = f(Fun({x, N}, f(_, x)), _);
    std::cout << F << "\n";
    std::cout << replace_placeholders_with_metavars(F, mgen) << "\n";
}

static void tst23() {
    environment env;
    substitution subst;
    unification_constraints_dbg up;
    metavar_generator mgen;
    type_checker checker(env);
    expr N  = Const("N");
    expr f  = Const("f");
    expr a  = Const("a");
    env.add_var("N", Type());
    env.add_var("f", N >> (N >> N));
    env.add_var("a", N);
    expr x  = Const("x");
    expr F0 = f(Fun({x, N}, f(_, x))(a), _);
    expr F1 = replace_placeholders_with_metavars(F0, mgen);
    std::cout << F1 << "\n";
    std::cout << checker.infer_type(F1, context(), &subst, &mgen, &up) << "\n";
    std::cout << up << "\n";
}

static void tst24() {
    substitution subst;
    metavar_generator gen;
    expr m1 = gen.mk();
    expr m2 = gen.mk();
    expr f  = Const("f");
    expr a  = Const("a");
    subst.assign(m1, f(m2));
    subst.assign(m2, a);
    lean_assert(instantiate_metavars(f(m1), subst) == f(f(a)));
    std::cout << instantiate_metavars(f(m1), subst) << "\n";
}

static void tst25() {
    environment env;
    substitution subst;
    unification_constraints_dbg up;
    metavar_generator gen;
    type_checker checker(env);
    expr N = Const("N");
    expr a = Const("a");
    expr b = Const("b");
    env.add_var("N", Type());
    env.add_var("a", N);
    env.add_var("b", N);
    expr m = gen.mk();
    expr F = m(a, b);
    std::cout << checker.infer_type(F, context(), &subst, &gen, &up) << "\n";
    std::cout << subst << "\n";
    std::cout << up << "\n";
}

int main() {
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
    tst21();
    tst22();
    tst23();
    tst24();
    tst25();
    return has_violations() ? 1 : 0;
}
