/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <algorithm>
#include <vector>
#include <utility>
#include <set>
#include "util/test.h"
#include "util/buffer.h"
#include "kernel/metavar.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
// #include "kernel/free_vars.h"
// #include "kernel/normalizer.h"
// #include "kernel/environment.h"
// #include "kernel/type_checker.h"
// #include "kernel/kernel_exception.h"
// #include "kernel/kernel.h"
// #include "kernel/io_state.h"
// #include "library/printer.h"
// #include "library/io_state_stream.h"
// #include "library/placeholder.h"
// #include "library/arith/arith.h"
// #include "frontends/lean/frontend.h"
// #include "frontends/lua/register_modules.h"
using namespace lean;

void collect_assumptions(justification const & j, buffer<unsigned> & r) {
    std::set<unsigned> already_found;
    buffer<justification> todo;
    todo.push_back(j);
    while (!todo.empty()) {
        justification j = todo.back();
        todo.pop_back();
        if (j.is_assumption()) {
            unsigned idx = assumption_idx(j);
            if (already_found.find(idx) == already_found.end()) {
                already_found.insert(idx);
                r.push_back(idx);
            }
        } else if (j.is_composite()) {
            todo.push_back(composite_child1(j));
            todo.push_back(composite_child2(j));
        }
    }
}

void display_assumptions(std::ostream & out, justification const & j) {
    buffer<unsigned> ids;
    collect_assumptions(j, ids);
    for (unsigned i = 0; i < ids.size(); i++) {
        if (i > 0) out << " ";
        out << ids[i];
    }
}

static std::ostream & operator<<(std::ostream & out, substitution const & s) {
    bool first = true;
    s.for_each([&](name const & n, expr const & v, justification const & j) {
            if (first) first = false; else out << "\n";
            out << "?" << n << " <- " << v << " {";
            display_assumptions(out, j);
            out << "}";
        });
    return out;
}

static bool check_assumptions(justification const & j, std::initializer_list<unsigned> const & ls) {
    buffer<unsigned> ids;
    collect_assumptions(j, ids);
    lean_assert(ids.size() == ls.size());
    for (unsigned id : ls) {
        lean_assert(std::find(ids.begin(), ids.end(), id) != ids.end());
    }
    return true;
}

static void tst1() {
    substitution subst;
    expr m1 = mk_metavar("m1", Bool);
    lean_assert(!subst.is_assigned(m1));
    expr m2 = mk_metavar("m2", Bool);
    lean_assert(!is_eqp(m1, m2));
    lean_assert(m1 != m2);
    expr f = Const("f");
    expr a = Const("a");
    subst.assign(m1, f(a));
    lean_assert(subst.is_assigned(m1));
    lean_assert(!subst.is_assigned(m2));
    lean_assert(*subst.get_expr(m1) == f(a));
    lean_assert(subst.instantiate_metavars(f(m1)).first == f(f(a)));
    std::cout << subst << "\n";
}

static void tst2() {
    substitution s;
    expr m1 = mk_metavar("m1", Bool);
    expr m2 = mk_metavar("m2", Bool);
    expr m3 = mk_metavar("m3", Bool);
    expr f = Const("f");
    expr g = Const("g");
    expr a = Const("a");
    s.assign(m1, f(m2), mk_assumption_justification(1));
    s.assign(m2, g(a),  mk_assumption_justification(2));
    lean_assert(check_assumptions(s.get_assignment(m1)->second, {1}));
    lean_assert(s.occurs(m1, f(m1)));
    lean_assert(s.occurs(m2, f(m1)));
    lean_assert(!s.occurs(m1, f(m2)));
    lean_assert(!s.occurs(m1, f(a)));
    lean_assert(!s.occurs(m3, f(m1)));
    std::cout << s << "\n";
    auto p1 = s.instantiate_metavars(g(m1));
    check_assumptions(p1.second, {1, 2});
    lean_assert(check_assumptions(s.get_assignment(m1)->second, {1}));
    lean_assert(p1.first == g(f(g(a))));
    auto p2 = s.d_instantiate_metavars(g(m1));
    check_assumptions(p2.second, {1, 2});
    std::cout << s << "\n";
    lean_assert(check_assumptions(s.get_assignment(m1)->second, {1, 2}));
}

#if 0
static void tst2() {
    metavar_env menv;
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr a = Const("a");
    expr T = Const("T");
    expr m1 = menv->mk_metavar(context({{"x", T}, {"y", T}}));
    expr m2 = menv->mk_metavar(context({{"x", T}, {"y", T}}));
    // move m1 to a different context, and store new metavariable + context in m11
    std::cout << "---------------------\n";
    expr m11 = add_inst(m1, 0, f(a, m2));
    std::cout << m11 << "\n";
    menv->assign(m1, f(Var(0)));
    std::cout << menv->instantiate_metavars(m11) << "\n";
    menv->assign(m2, g(a, Var(1)));
    std::cout << menv->instantiate_metavars(h(m11)) << "\n";
    lean_assert_eq(menv->instantiate_metavars(h(m11)), h(f(f(a, g(a, Var(1))))));
}

static void tst3() {
    metavar_env menv;
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr a = Const("a");
    expr x = Const("x");
    expr T = Const("T");
    expr m1 = menv->mk_metavar(context({{"x", T}, {"y", T}, {"z", T}}));
    expr F = Fun({x, T}, f(m1, x));
    menv->assign(m1, h(Var(0), Var(2)));
    std::cout << instantiate(abst_body(F), g(a)) << "\n";
    lean_assert(menv->instantiate_metavars(instantiate(abst_body(F), g(a))) == f(h(g(a), Var(1)), g(a)));
    std::cout << instantiate(menv->instantiate_metavars(abst_body(F)), g(a)) << "\n";
    lean_assert(instantiate(menv->instantiate_metavars(abst_body(F)), g(a)) ==
                menv->instantiate_metavars(instantiate(abst_body(F), g(a))));
}

static void tst4() {
    metavar_env menv;
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr a = Const("a");
    expr T = Const("T");
    expr m1 = menv->mk_metavar(context({{"x", T}, {"y", T}}));
    expr F = f(m1, Var(2));
    menv->assign(m1, h(Var(1)));
    std::cout << instantiate(F, {g(Var(0)), h(a)}) << "\n";
    std::cout << menv->instantiate_metavars(instantiate(F, {g(Var(0)), h(a)})) << "\n";
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
    expr T  = Const("T");
    expr m1 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}, {"x4", T}}));
    expr m2 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}, {"x4", T}}));
    expr t = f(Var(0), Fun({x, N}, f(Var(1), x, Fun({y, N}, f(Var(2), x, y)))));
    expr r = instantiate(t, g(m1, m2));
    std::cout << r << std::endl;
    menv->assign(m2, Var(2));
    r = menv->instantiate_metavars(r);
    std::cout << r << std::endl;
    menv->assign(m1, h(Var(3)));
    r = menv->instantiate_metavars(r);
    std::cout << r << std::endl;
    lean_assert(r == f(g(h(Var(3)), Var(2)), Fun({x, N}, f(g(h(Var(4)), Var(3)), x, Fun({y, N}, f(g(h(Var(5)), Var(4)), x, y))))));
}

static void tst7() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    metavar_env menv;
    expr T  = Const("T");
    expr m1 = menv->mk_metavar(context({{"x", T}}));
    expr t  = f(m1, Var(0));
    expr r = instantiate(t, a);
    menv->assign(m1, g(Var(0)));
    r = menv->instantiate_metavars(r);
    std::cout << r << std::endl;
    lean_assert(r == f(g(a), a));
}

static void tst8() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    metavar_env menv;
    expr T  = Const("T");
    expr m1 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}, {"x4", T}}));
    expr t  = f(m1, Var(0), Var(2));
    expr r = instantiate(t, a);
    menv->assign(m1, g(Var(0), Var(1)));
    r = menv->instantiate_metavars(r);
    std::cout << r << std::endl;
    lean_assert(r == f(g(a, Var(0)), a, Var(1)));
}

static void tst9() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    metavar_env menv;
    expr T  = Const("T");
    expr m1 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}, {"x4", T}}));
    expr t  = f(m1, Var(1), Var(2));
    expr r  = lift_free_vars(t, 1, 2);
    std::cout << r << std::endl;
    r = instantiate(r, a);
    std::cout << r << std::endl;
    menv->assign(m1, g(Var(0), Var(1)));
    r = menv->instantiate_metavars(r);
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
    expr T  = Const("T");
    expr m1 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}, {"x4", T}}));
    expr m2 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}, {"x4", T}}));
    expr t = f(Var(0), Fun({x, N}, f(Var(1), Var(2), x, Fun({y, N}, f(Var(2), x, y)))));
    expr r = instantiate(t, g(m1));
    std::cout << r << std::endl;
    r = instantiate(r, h(m2));
    std::cout << r << std::endl;
    menv->assign(m1, f(Var(0)));
    menv->assign(m2, Var(2));
    r = menv->instantiate_metavars(r);
    std::cout << r << std::endl;
    lean_assert(r == f(g(f(h(Var(2)))), Fun({x, N}, f(g(f(h(Var(3)))), h(Var(3)), x, Fun({y, N}, f(g(f(h(Var(4)))), x, y))))));
}

static void tst11() {
    metavar_env menv;
    unsigned t1 = menv->get_timestamp();
    expr m = menv->mk_metavar();
    unsigned t2 = menv->get_timestamp();
    lean_assert(t2 > t1);
    lean_assert(!menv->is_assigned(m));
    lean_assert(menv->get_timestamp() == t2);
    menv->assign(m, Const("a"));
    lean_assert(menv->get_timestamp() > t2);
}

static void tst12() {
    metavar_env menv;
    expr T  = Const("T");
    expr m = menv->mk_metavar(context({{"x1", T}, {"x2", T}}));
    expr f = Const("f");
    std::cout << instantiate(f(m), {Var(0), Var(1)}) << "\n";
    std::cout << instantiate(f(m), {Var(1), Var(0)}) << "\n";
}

static void tst13() {
    environment env;
    metavar_env menv;
    expr T  = Const("T");
    expr m = menv->mk_metavar(context({{"x", T}}));
    env->add_var("N", Type());
    expr N = Const("N");
    env->add_var("f", N >> N);
    expr f = Const("f");
    env->add_var("a", N);
    expr a = Const("a");
    expr x = Const("x");
    expr F = Fun({x, N}, f(m))(a);
    normalizer norm(env);
    std::cout << norm(F) << "\n";
    menv->assign(m, Var(0));
    std::cout << norm(menv->instantiate_metavars(F)) << "\n";
    lean_assert(norm(menv->instantiate_metavars(F)) ==
                menv->instantiate_metavars(norm(F)));
}

static void tst14() {
    environment env;
    metavar_env menv;
    expr T  = Const("T");
    expr m1 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}, {"x4", T}, {"x5", T}}));
    expr m2 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}, {"x4", T}, {"x5", T}}));
    expr N = Const("N");
    expr f = Const("f");
    expr h = Const("h");
    expr a = Const("a");
    expr b = Const("b");
    expr x = Const("x");
    expr y = Const("y");
    env->add_var("h", Pi({N, Type()}, N >> (N >> N)));
    expr F1 = Fun({{N, Type()}, {a, N}, {f, N >> N}},
                  (Fun({{x, N}, {y, N}}, mk_eq(N, f(m1), y)))(a));
    metavar_env menv2 = menv.copy();
    menv2->assign(m1, h(Var(4), Var(1), Var(3)));
    normalizer norm(env);
    env->add_var("M", Type());
    expr M = Const("M");
    std::cout << norm(F1) << "\n";
    std::cout << menv2->instantiate_metavars(norm(F1)) << "\n";
    std::cout << menv2->instantiate_metavars(F1) << "\n";
    std::cout << norm(menv2->instantiate_metavars(F1)) << "\n";
    lean_assert(menv2->instantiate_metavars(norm(F1)) ==
                norm(menv2->instantiate_metavars(F1)));
}

static void tst15() {
    environment env;
    metavar_env menv;
    normalizer  norm(env);
    expr T  = Const("T");
    expr m1 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}}));
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    env->add_var("N", Type());
    env->add_var("f", Type() >> Type());
    expr F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}}, f(m1))(N, N));
    menv->assign(m1, Var(2));
    std::cout << norm(F) << "\n";
    std::cout << menv->instantiate_metavars(norm(F)) << "\n";
    std::cout << norm(menv->instantiate_metavars(F)) << "\n";
    lean_assert(menv->instantiate_metavars(norm(F)) ==
                norm(menv->instantiate_metavars(F)));
}

static void tst16() {
    environment env;
    metavar_env menv;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w", Type());
    expr T  = Const("T");
    expr m1 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}, {"x4", T}, {"x5", T}}));
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    env->add_var("N", Type());
    expr F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}}, m1)(N, N));
    menv->assign(m1, Var(3));
    std::cout << norm(F, ctx) << "\n";
    std::cout << menv->instantiate_metavars(norm(F, ctx)) << "\n";
    std::cout << norm(menv->instantiate_metavars(F), ctx) << "\n";
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
    expr T  = Const("T");
    expr m1 = menv->mk_metavar(context({{"x1", T}, {"x2", T}, {"x3", T}, {"x4", T}}));
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    env->add_var("N", Type());
    expr F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}}, m1)(N, N));
    metavar_env menv2 = menv.copy();
    menv->assign(m1, Var(3));
    std::cout << norm(F, ctx) << "\n";
    std::cout << menv->instantiate_metavars(norm(F, ctx)) << "\n";
    std::cout << norm(menv->instantiate_metavars(F), ctx) << "\n";
    F = Fun({z, Type()}, Fun({{x, Type()}, {y, Type()}, {x, Type()}, {y, Type()}, {x, Type()}}, m1)(N, N, N, N, N));
    lean_assert(menv->instantiate_metavars(norm(F, ctx)) ==
                norm(menv->instantiate_metavars(F), ctx));
    std::cout << "----------------------\n";
    menv2->assign(m1, Var(8));
    std::cout << norm(F, ctx) << "\n";
    std::cout << menv2->instantiate_metavars(norm(F, ctx)) << "\n";
    std::cout << norm(menv2->instantiate_metavars(F), ctx) << "\n";
    lean_assert(menv2->instantiate_metavars(norm(F, ctx)) ==
                norm(menv2->instantiate_metavars(F), ctx));
}

static void tst18() {
    environment env;
    metavar_env menv;
    normalizer  norm(env);
    expr f = Const("f");
    expr g = Const("g");
    expr h = Const("h");
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    expr a = Const("a");
    context ctx({{"x1", N}});
    env->add_var("N", Type());
    env->add_var("a", N);
    env->add_var("g", N >> N);
    env->add_var("h", N >> (N >> N));
    expr m1 = menv->mk_metavar(context({{"x1", N}, {"z", Type()}, {"f", N >> N}, {"y", Type()}}));
    expr m2 = menv->mk_metavar(context({{"x1", N}, {"z", Type()}, {"x", N}}));
    expr F = Fun({z, Type()}, Fun({{f, N >> N}, {y, Type()}}, m1)(Fun({x, N}, g(z, x, m2)), N));
    std::cout << norm(F, ctx) << "\n";
    metavar_env menv2 = menv.copy();
    menv2->assign(m1, Var(1));
    menv2->assign(m2, h(Var(2), Var(1)));
    std::cout << menv2->instantiate_metavars(norm(F, ctx)) << "\n";
    std::cout << menv2->instantiate_metavars(F) << "\n";
    lean_assert_eq(menv2->instantiate_metavars(norm(F, ctx, menv2)),
                   norm(menv2->instantiate_metavars(F), ctx, menv2));
    std::cout << "norm(F...): " << norm(F, ctx, menv2) << "\n";
    lean_assert(menv2->is_assigned(m1));
    lean_assert(menv2->is_assigned(m2));
    lean_assert_eq(menv2->instantiate_metavars(norm(F, ctx, menv2)),
                   Fun({{z, Type()}, {x, N}}, g(z, x, h(Var(2), z))));
}

static void tst19() {
    environment env;
    metavar_env menv;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w1", Type());
    ctx = extend(ctx, "w2", Type());
    expr x  = Const("x");
    expr y  = Const("y");
    expr N  = Const("N");
    expr m1 = menv->mk_metavar(context({{"N", Type()}, {"x", N}, {"y", N}}));
    expr F  = Fun({{N, Type()}, {x, N}, {y, N}}, m1);
    std::cout << norm(F) << "\n";
    std::cout << norm(F, ctx) << "\n";
    lean_assert_eq(norm(F, context(), menv), F);
    lean_assert_eq(norm(F, ctx, menv), F);
}

static void tst20() {
    environment env;
    metavar_env menv;
    normalizer  norm(env);
    context ctx;
    ctx = extend(ctx, "w1", Type());
    ctx = extend(ctx, "w2", Type());
    expr x = Const("x");
    expr y = Const("y");
    expr z = Const("z");
    expr N = Const("N");
    expr a = Const("a");
    expr b = Const("b");
    expr m1 = menv->mk_metavar(context({{"x", N}, {"y", N}, {"z", N}, {"x", N}, {"y", N}}));
    env->add_var("N", Type());
    env->add_var("a", N);
    env->add_var("b", N);
    expr F = Fun({{x, N}, {y, N}, {z, N}}, Fun({{x, N}, {y, N}}, m1)(a, b));
    std::cout << norm(F) << "\n";
    std::cout << norm(F, ctx) << "\n";
}

static void tst21() {
    metavar_env menv;
    expr m1 = menv->mk_metavar();
    expr l  = add_lift(add_lift(m1, 0, 1), 1, 1);
    expr r  = add_lift(m1, 0, 2);
    std::cout << menv->get_type(l) << " " << menv->get_type(r) << "\n";
#if 0
    // Leo: I disabled the lift over lift optimization since it was
    // negatively impacting the heuristics
    lean_assert_eq(l, r);
    lean_assert_eq(add_lift(add_lift(m1, 1, 2), 3, 4),
                   add_lift(m1, 1, 6));
    lean_assert_eq(add_lift(add_lift(m1, 1, 3), 3, 4),
                   add_lift(m1, 1, 7));
    lean_assert_ne(add_lift(add_lift(m1, 0, 3), 3, 4),
                   add_lift(m1, 1, 7));
#endif
}

#define _ mk_placeholder()

static void tst22() {
    metavar_env menv;
    expr f = Const("f");
    expr x = Const("x");
    expr N = Const("N");
    expr F = f(Fun({x, N}, f(_, x)), _);
    std::cout << F << "\n";
    std::cout << replace_placeholders_with_metavars(F, menv) << "\n";
}

static void tst23() {
    environment env;
    metavar_env menv;
    type_checker checker(env);
    expr N  = Const("N");
    expr f  = Const("f");
    expr a  = Const("a");
    env->add_var("N", Type());
    env->add_var("f", N >> (N >> N));
    env->add_var("a", N);
    expr x  = Const("x");
    expr F0 = f(Fun({x, N}, f(_, x))(a), _);
    expr F1 = replace_placeholders_with_metavars(F0, menv);
    buffer<unification_constraint> up;
    std::cout << F1 << "\n";
    try {
        std::cout << checker.check(F1, context(), menv, up) << "\n";
    } catch (kernel_exception & ex) {
        formatter fmt = mk_simple_formatter();
        io_state st(options(), fmt);
        regular(st) << ex << "\n";
    }
    std::cout << up << "\n";
}

static void tst24() {
    metavar_env menv;
    expr m1 = menv->mk_metavar();
    expr m2 = menv->mk_metavar();
    expr f  = Const("f");
    expr a  = Const("a");
    menv->assign(m1, f(m2));
    menv->assign(m2, a);
    lean_assert(menv->instantiate_metavars(f(m1)) == f(f(a)));
    std::cout << menv->instantiate_metavars(f(m1)) << "\n";
}

static void tst25() {
    environment env;
    metavar_env menv;
    buffer<unification_constraint> up;
    type_checker checker(env);
    expr N = Const("N");
    expr a = Const("a");
    expr b = Const("b");
    env->add_var("N", Type());
    env->add_var("a", N);
    env->add_var("b", N);
    expr m = menv->mk_metavar();
    expr F = m(a, b);
    std::cout << checker.check(F, context(), menv, up) << "\n";
    std::cout << menv << "\n";
    std::cout << up << "\n";
}

static void tst26() {
    /*
      Encoding the following problem

      Variable list : Type -> Type
      Variable nil  {A : Type} : list A
      Variable cons {A : Type} (head : A) (tail : list A) : list A
      Variables a b : Int
      Variables n m : Nat
      Definition l2 : list Int := cons a (cons n (cons b nil))
    */
    std::cout << "\ntst26\n";
    environment  env;
    init_test_frontend(env);
    metavar_env menv;
    buffer<unification_constraint> up;
    type_checker checker(env);
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
    std::cout << checker.check(F, context(), menv, up) << "\n";
    std::cout << menv << "\n";
    std::cout << up << "\n";
}

static void tst27() {
    /*
      Variable f {A : Type} (a b : A) : Bool
      Variable a : Int
      Variable b : Real
      Definition tst : Bool := (fun x y, f x y) a b
    */
    std::cout << "\ntst27\n";
    environment  env;
    init_test_frontend(env);
    metavar_env menv;
    buffer<unification_constraint> up;
    type_checker checker(env);
    expr A    = Const("A");
    expr f    = Const("f");
    expr a    = Const("a");
    expr b    = Const("b");
    expr x    = Const("x");
    expr y    = Const("y");
    env->add_var("f", Pi({A, Type()}, A >> (A >> Bool)));
    env->add_var("a", Int);
    env->add_var("b", Real);
    expr T1 = menv->mk_metavar();
    expr T2 = menv->mk_metavar(context({{"x", T1}}));
    expr A1 = menv->mk_metavar(context({{"x", T1}, {"y", T2}}));
    expr m1 = menv->mk_metavar(context({{"x", T1}, {"y", T2}}));
    expr m2 = menv->mk_metavar(context({{"x", T1}, {"y", T2}}));
    expr F = Fun({{x, T1}, {y, T2}}, f(A1, x, y))(m1(a), m2(b));
    std::cout << F << "\n";
    std::cout << checker.check(F, context(), menv, up) << "\n";
    std::cout << menv << "\n";
    std::cout << up << "\n";
}

static void tst28() {
    metavar_env menv;
    expr f = Const("f");
    expr a = Const("a");
    expr m1 = menv->mk_metavar();
    lean_assert(add_inst(m1, 0, f(a), menv) == m1);
    lean_assert(add_inst(m1, 1, f(a), menv) == m1);
    lean_assert(add_lift(m1, 0, 2, menv) == m1);
    lean_assert(add_lift(m1, 1, 2, menv) == m1);
    expr m2 = menv->mk_metavar(context({{"x", Bool}, {"y", Bool}}));
    lean_assert(add_inst(m2, 0, f(a), menv) != m2);
    lean_assert(add_inst(m2, 0, f(a), menv) == add_inst(m2, 0, f(a)));
    lean_assert(add_inst(m2, 1, f(a), menv) != m2);
    lean_assert(add_inst(m2, 2, f(a), menv) == m2);
    lean_assert(add_lift(m2, 0, 2, menv) != m2);
    lean_assert(add_lift(m2, 0, 2, menv) == add_lift(m2, 0, 2));
    lean_assert(add_lift(m2, 1, 2, menv) != m2);
    lean_assert(add_lift(m2, 2, 2, menv) == m2);
    lean_assert(add_lift(m2, 2, 2, menv) != add_lift(m2, 2, 2));
}
#endif

int main() {
    save_stack_info();
    tst1();
    tst2();
#if 0
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
    tst26();
    tst27();
    tst28();
#endif
    return has_violations() ? 1 : 0;
}
