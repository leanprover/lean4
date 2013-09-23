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

class unification_problems_dbg : public unification_problems {
    typedef std::tuple<context, expr, expr> constraint;
    typedef std::vector<constraint>         constraints;
    constraints m_eqs;
    constraints m_type_of_eqs;
    constraints m_is_convertible_cnstrs;
public:
    unification_problems_dbg() {}
    virtual ~unification_problems_dbg() {}
    virtual void add_eq(context const & ctx, expr const & lhs, expr const & rhs) { m_eqs.push_back(constraint(ctx, lhs, rhs)); }
    virtual void add_type_of_eq(context const & ctx, expr const & n, expr const & t) { m_type_of_eqs.push_back(constraint(ctx, n, t)); }
    virtual void add_is_convertible(context const & ctx, expr const & t1, expr const & t2) { m_is_convertible_cnstrs.push_back(constraint(ctx, t1, t2)); }
    constraints const & eqs() const { return m_eqs; }
    constraints const & type_of_eqs() const { return m_type_of_eqs; }
    constraints const & is_convertible_cnstrs() const { return m_is_convertible_cnstrs; }
    friend std::ostream & operator<<(std::ostream & out, unification_problems_dbg const & up) {
        for (auto c : up.m_eqs)
            std::cout << std::get<0>(c) << " |- " << std::get<1>(c) << " == " << std::get<2>(c) << "\n";
        for (auto c : up.m_type_of_eqs)
            std::cout << std::get<0>(c) << " |- " << std::get<1>(c) << " : " << std::get<2>(c) << "\n";
        for (auto c : up.m_is_convertible_cnstrs)
            std::cout << std::get<0>(c) << " |- " << std::get<1>(c) << " == " << std::get<2>(c) << "\n";
        return out;
    }
};

std::ostream & operator<<(std::ostream & out, metavar_env const & env) {
    bool first = true;
    for (unsigned i = 0; i < env.size(); i++) {
        if (env.is_assigned(i)) {
            if (first) first = false; else out << "\n";
            out << "?M" << i << " <- " << env.get_subst(i);
        }
    }
    return out;
}

static void tst1() {
    unification_problems_dbg u;
    metavar_env          menv;
    expr m1 = menv.mk_metavar();
    lean_assert(!menv.is_assigned(m1));
    lean_assert(menv.contains(m1));
    lean_assert(!menv.contains(2));
    expr t1 = menv.get_type(m1, u);
    lean_assert(is_metavar(t1));
    lean_assert(menv.contains(t1));
    lean_assert(is_eqp(menv.get_type(m1, u), t1));
    lean_assert(is_eqp(menv.get_type(m1, u), t1));
    lean_assert(!menv.is_assigned(m1));
    expr m2 = menv.mk_metavar();
    lean_assert(!menv.is_assigned(m1));
    lean_assert(menv.contains(m1));
    expr t2 = menv.get_type(m2, u);
    lean_assert(is_metavar(m2));
    lean_assert(menv.contains(m2));
    lean_assert(!is_eqp(t1, t2));
    lean_assert(t1 != t2);
    lean_assert(u.eqs().empty());
    lean_assert(u.type_of_eqs().size() == 2);
    for (auto p : u.type_of_eqs()) {
        std::cout << "typeof(" << std::get<1>(p) << ") == " << std::get<2>(p) << "\n";
    }
    expr f = Const("f");
    expr a = Const("a");
    menv.assign(m1, f(a));
    lean_assert(menv.is_assigned(m1));
    lean_assert(!menv.is_assigned(m2));
    lean_assert(menv.get_subst(m1) == f(a));
}

static void tst2() {
    metavar_env menv;
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr a = Const("a");
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    // move m1 to a different context, and store new metavariable + context in m11
    std::cout << "---------------------\n";
    expr m11 = add_inst(m1, 0, f(a, m2));
    std::cout << m11 << "\n";
    menv.assign(m1, f(Var(0)));
    std::cout << instantiate_metavars(m11, menv) << "\n";
    menv.assign(m2, g(a, Var(1)));
    std::cout << instantiate_metavars(h(m11), menv) << "\n";
    lean_assert(instantiate_metavars(h(m11), menv) == h(f(f(a, g(a, Var(1))))));
}

static void tst3() {
    metavar_env menv;
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr a = Const("a");
    expr x = Const("x");
    expr T = Const("T");
    expr m1 = menv.mk_metavar();
    expr F = Fun({x, T}, f(m1, x));
    menv.assign(m1, h(Var(0), Var(2)));
    std::cout << instantiate(abst_body(F), g(a)) << "\n";
    std::cout << instantiate_metavars(instantiate(abst_body(F), g(a)), menv) << "\n";
    lean_assert(instantiate_metavars(instantiate(abst_body(F), g(a)), menv) == f(h(g(a), Var(1)), g(a)));
    std::cout << instantiate(instantiate_metavars(abst_body(F), menv), g(a)) << "\n";
    lean_assert(instantiate(instantiate_metavars(abst_body(F), menv), g(a)) ==
                instantiate_metavars(instantiate(abst_body(F), g(a)), menv));
}

static void tst4() {
    metavar_env menv;
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr a = Const("a");
    expr m1 = menv.mk_metavar();
    expr F = f(m1, Var(2));
    menv.assign(m1, h(Var(1)));
    std::cout << instantiate(F, {g(Var(0)), h(a)}) << "\n";
    std::cout << instantiate_metavars(instantiate(F, {g(Var(0)), h(a)}), menv) << "\n";
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
    metavar_env menv;
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr t = f(Var(0), Fun({x, N}, f(Var(1), x, Fun({y, N}, f(Var(2), x, y)))));
    expr r = instantiate(t, g(m1, m2));
    std::cout << r << std::endl;
    menv.assign(1, Var(2));
    r = instantiate_metavars(r, menv);
    std::cout << r << std::endl;
    menv.assign(0, h(Var(3)));
    r = instantiate_metavars(r, menv);
    std::cout << r << std::endl;
    lean_assert(r == f(g(h(Var(3)), Var(2)), Fun({x, N}, f(g(h(Var(4)), Var(3)), x, Fun({y, N}, f(g(h(Var(5)), Var(4)), x, y))))));
}

static void tst7() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    metavar_env menv;
    expr m1 = menv.mk_metavar();
    expr t  = f(m1, Var(0));
    expr r = instantiate(t, a);
    menv.assign(0, g(Var(0)));
    r = instantiate_metavars(r, menv);
    std::cout << r << std::endl;
    lean_assert(r == f(g(a), a));
}

static void tst8() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    metavar_env menv;
    expr m1 = menv.mk_metavar();
    expr t  = f(m1, Var(0), Var(2));
    expr r = instantiate(t, a);
    menv.assign(0, g(Var(0), Var(1)));
    r = instantiate_metavars(r, menv);
    std::cout << r << std::endl;
    lean_assert(r == f(g(a, Var(0)), a, Var(1)));
}

static void tst9() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    metavar_env menv;
    expr m1 = menv.mk_metavar();
    expr t  = f(m1, Var(1), Var(2));
    expr r  = lift_free_vars(t, 1, 2);
    std::cout << r << std::endl;
    r = instantiate(r, a);
    std::cout << r << std::endl;
    menv.assign(0, g(Var(0), Var(1)));
    r = instantiate_metavars(r, menv);
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
    metavar_env menv;
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr t = f(Var(0), Fun({x, N}, f(Var(1), Var(2), x, Fun({y, N}, f(Var(2), x, y)))));
    expr r = instantiate(t, g(m1));
    std::cout << r << std::endl;
    r = instantiate(r, h(m2));
    std::cout << r << std::endl;
    menv.assign(0, f(Var(0)));
    menv.assign(1, Var(2));
    r = instantiate_metavars(r, menv);
    std::cout << r << std::endl;
    lean_assert(r == f(g(f(h(Var(2)))), Fun({x, N}, f(g(f(h(Var(3)))), h(Var(3)), x, Fun({y, N}, f(g(f(h(Var(4)))), x, y))))));
}

static void tst11() {
    metavar_env menv;
    unsigned t1 = menv.get_timestamp();
    expr m = menv.mk_metavar();
    unsigned t2 = menv.get_timestamp();
    lean_assert(t2 > t1);
    lean_assert(!menv.is_assigned(m));
    lean_assert(menv.get_timestamp() == t2);
    menv.assign(m, Const("a"));
    lean_assert(menv.get_timestamp() > t2);
}

static void tst12() {
    metavar_env menv;
    expr m = menv.mk_metavar();
    expr f = Const("f");
    std::cout << instantiate(f(m), {Var(0), Var(1)}) << "\n";
    std::cout << instantiate(f(m), {Var(1), Var(0)}) << "\n";
}

static void tst13() {
    environment env;
    metavar_env menv;
    expr m = menv.mk_metavar();
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
    menv.assign(0, Var(0));
    std::cout << norm(instantiate_metavars(F, menv)) << "\n";
    lean_assert(norm(instantiate_metavars(F, menv)) ==
                instantiate_metavars(norm(F), menv));
}

static void tst14() {
    environment env;
    metavar_env menv;
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
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
    metavar_env menv2 = menv;
    menv2.assign(0, h(Var(4), Var(1), Var(3)));
    normalizer norm(env);
    env.add_var("M", Type());
    expr M = Const("M");
    std::cout << norm(F1) << "\n";
    std::cout << instantiate_metavars(norm(F1), menv2) << "\n";
    std::cout << instantiate_metavars(F1, menv2) << "\n";
    std::cout << norm(instantiate_metavars(F1, menv2)) << "\n";
    lean_assert(instantiate_metavars(norm(F1), menv2) ==
                norm(instantiate_metavars(F1, menv2)));
    expr F2 = (Fun({{N, Type()}, {f, N >> N}, {a, N}, {b, N}},
                   (Fun({{x, N}, {y, N}}, Eq(f(m1), y)))(a, m2)))(M);
    std::cout << norm(F2) << "\n";
    expr F3 = (Fun({{N, Type()}, {f, N >> N}, {a, N}, {b, N}},
                   (Fun({{x, N}, {y, N}}, Eq(f(m1), y)))(b, m2)))(M);
    std::cout << norm(F3) << "\n";
}

static void tst15() {
    environment env;
    metavar_env menv;
    normalizer  norm(env);
    expr m1 = menv.mk_metavar();
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    env.add_var("N", Type());
    env.add_var("f", Type() >> Type());
    expr F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}}, f(m1))(N, N));
    menv.assign(0, Var(2));
    std::cout << norm(F) << "\n";
    std::cout << instantiate_metavars(norm(F), menv) << "\n";
    std::cout << norm(instantiate_metavars(F, menv)) << "\n";
    lean_assert(instantiate_metavars(norm(F), menv) ==
                norm(instantiate_metavars(F, menv)));
}

static void tst16() {
    environment env;
    metavar_env menv;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w", Type());
    expr m1 = menv.mk_metavar();
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    env.add_var("N", Type());
    expr F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}}, m1)(N, N));
    menv.assign(0, Var(3));
    std::cout << norm(F, ctx) << "\n";
    std::cout << instantiate_metavars(norm(F, ctx), menv) << "\n";
    std::cout << norm(instantiate_metavars(F, menv), ctx) << "\n";
}

static void tst17() {
    environment env;
    metavar_env menv;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w1", Type());
    ctx = extend(ctx, "w2", Type());
    ctx = extend(ctx, "w3", Type());
    ctx = extend(ctx, "w4", Type());
    expr m1 = menv.mk_metavar();
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    env.add_var("N", Type());
    expr F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}}, m1)(N, N));
    metavar_env menv2 = menv;
    menv.assign(0, Var(3));
    std::cout << norm(F, ctx) << "\n";
    std::cout << instantiate_metavars(norm(F, ctx), menv) << "\n";
    std::cout << norm(instantiate_metavars(F, menv), ctx) << "\n";
    F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}, {x, Type()}, {y, Type()}, {x, Type()}}, m1)(N, N, N, N, N));
    lean_assert(instantiate_metavars(norm(F, ctx), menv) ==
                norm(instantiate_metavars(F, menv), ctx));
    std::cout << "----------------------\n";
    menv2.assign(0, Var(8));
    std::cout << norm(F, ctx) << "\n";
    std::cout << instantiate_metavars(norm(F, ctx), menv2) << "\n";
    std::cout << norm(instantiate_metavars(F, menv2), ctx) << "\n";
    lean_assert(instantiate_metavars(norm(F, ctx), menv2) ==
                norm(instantiate_metavars(F, menv2), ctx));
}

static void tst18() {
    environment env;
    metavar_env menv;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w1", Type());
    ctx = extend(ctx, "w2", Type());
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
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
    metavar_env menv2 = menv;
    menv2.assign(0, Var(1));
    menv2.assign(1, h(Var(2), Var(1)));
    std::cout << instantiate_metavars(norm(F, ctx), menv2) << "\n";
    std::cout << instantiate_metavars(F, menv2) << "\n";
    lean_assert(instantiate_metavars(norm(F, ctx), menv2) ==
                norm(instantiate_metavars(F, menv2), ctx));
    lean_assert(instantiate_metavars(norm(F, ctx), menv2) ==
                Fun({{z, Type()}, {x, N}}, g(z, x, h(Var(2), z))));
}

static void tst19() {
    environment env;
    metavar_env menv;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w1", Type());
    ctx = extend(ctx, "w2", Type());
    expr m1 = menv.mk_metavar();
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
    metavar_env menv;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w1", Type());
    ctx = extend(ctx, "w2", Type());
    expr m1 = menv.mk_metavar();
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
    metavar_env menv;
    expr m1 = menv.mk_metavar();
    lean_assert(add_lift(add_lift(m1, 0, 1), 1, 1) ==
                add_lift(m1, 0, 2));
    lean_assert(add_lift(add_lift(m1, 1, 2), 3, 4) ==
                add_lift(m1, 1, 6));
    lean_assert(add_lift(add_lift(m1, 1, 3), 3, 4) !=
                add_lift(m1, 1, 7));
}

#define _ mk_placholder()

static void tst22() {
    metavar_env menv;
    expr f = Const("f");
    expr x = Const("x");
    expr N = Const("N");
    expr F = f(Fun({x, N}, f(_, x)), _);
    std::cout << F << "\n";
    std::cout << replace_placeholders_with_metavars(F, menv) << "\n";
    lean_assert(menv.contains(0));
    lean_assert(menv.contains(1));
    lean_assert(!menv.contains(2));
    lean_assert(menv.get_context(0).size() == 1);
    lean_assert(lookup(menv.get_context(0), 0).get_domain() == N);
    lean_assert(menv.get_context(1).size() == 0);
}

static void tst23() {
    environment env;
    metavar_env menv;
    unification_problems_dbg up;
    type_checker checker(env);
    expr N  = Const("N");
    expr f  = Const("f");
    expr a  = Const("a");
    env.add_var("N", Type());
    env.add_var("f", N >> (N >> N));
    env.add_var("a", N);
    expr x  = Const("x");
    expr F0 = f(Fun({x, N}, f(_, x))(a), _);
    expr F1 = replace_placeholders_with_metavars(F0, menv);
    std::cout << F1 << "\n";
    std::cout << checker.infer_type(F1, context(), &menv, &up) << "\n";
    std::cout << up << "\n";
}

static void tst24() {
    metavar_env menv;
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr f  = Const("f");
    expr a  = Const("a");
    menv.assign(m1, f(m2));
    menv.assign(m2, a);
    lean_assert(instantiate_metavars(f(m1), menv) == f(f(a)));
    std::cout << instantiate_metavars(f(m1), menv) << "\n";
}

static void tst25() {
    environment env;
    metavar_env menv;
    unification_problems_dbg up;
    type_checker checker(env);
    expr N = Const("N");
    expr a = Const("a");
    expr b = Const("b");
    env.add_var("N", Type());
    env.add_var("a", N);
    env.add_var("b", N);
    expr m = menv.mk_metavar();
    expr F = m(a, b);
    std::cout << checker.infer_type(F, context(), &menv, &up) << "\n";
    std::cout << menv << "\n";
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
