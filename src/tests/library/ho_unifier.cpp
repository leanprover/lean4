/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/environment.h"
#include "kernel/builtin.h"
#include "kernel/abstract.h"
#include "library/ho_unifier.h"
#include "library/printer.h"
#include "library/reduce.h"
#include "library/arith/arith.h"
using namespace lean;

void tst1() {
    environment env;
    substitution subst;
    ho_unifier  unify(env);
    expr N  = Const("N");
    expr M  = Const("M");
    env.add_var("N", Type());
    env.add_var("M", Type());
    env.add_var("f", N >> (M >> M));
    env.add_var("a", N);
    env.add_var("b", M);
    expr f  = Const("f");
    expr x  = Const("x");
    expr a  = Const("a");
    expr b  = Const("b");
    expr m1; // = subst.mk_metavar();
    expr l = m1(b, a);
    expr r = f(b, f(a, b));
    for (auto sol : unify(context(), l, r, subst)) {
        std::cout << m1 << " -> " << beta_reduce(sol.first.get_subst(m1)) << "\n";
        std::cout << beta_reduce(instantiate_metavars(l, sol.first)) << "\n";
        lean_assert(beta_reduce(instantiate_metavars(l, sol.first)) == r);
        std::cout << "--------------\n";
    }
}

void tst2() {
    environment env;
    import_basic(env);
    substitution subst;
    ho_unifier  unify(env);
    expr N  = Const("N");
    expr M  = Const("M");
    env.add_var("N", Type());
    env.add_var("f", N >> (Bool >> N));
    env.add_var("a", N);
    env.add_var("b", N);
    expr f  = Const("f");
    expr x  = Const("x");
    expr a  = Const("a");
    expr b  = Const("b");
    expr m1; // = subst.mk_metavar();
    expr l = m1(b, a);
    expr r = Fun({x, N}, f(x, Eq(a, b)));
    for (auto sol : unify(context(), l, r, subst)) {
        std::cout << m1 << " -> " << beta_reduce(sol.first.get_subst(m1)) << "\n";
        std::cout << beta_reduce(instantiate_metavars(l, sol.first)) << "\n";
        lean_assert(beta_reduce(instantiate_metavars(l, sol.first)) == r);
        std::cout << "--------------\n";
    }
}

void tst3() {
    environment env;
    import_basic(env);
    import_arith(env);
    substitution subst;
    ho_unifier  unify(env);
    expr N  = Const("N");
    env.add_var("N", Type());
    env.add_var("f", N >> (Int >> N));
    env.add_var("a", N);
    env.add_var("b", N);
    expr m1; // = subst.mk_metavar();
    expr m2; // = subst.mk_metavar();
    expr m3; // = subst.mk_metavar();
    expr t1 = metavar_type(m1);
    expr t2 = metavar_type(m2);
    expr f  = Const("f");
    expr a  = Const("a");
    expr b  = Const("b");
    expr l = f(m1(a), iAdd(m3, iAdd(iVal(1), iVal(1))));
    expr r = f(m2(b), iAdd(iVal(1), iVal(2)));
    for (auto sol : unify(context(), l, r, subst)) {
        std::cout << m3 << " -> " << sol.first.get_subst(m3) << "\n";
        lean_assert(sol.first.get_subst(m3) == iVal(1));
        lean_assert(length(sol.second) == 1);
        for (auto c : sol.second) {
            std::cout << std::get<1>(c) << " == " << std::get<2>(c) << "\n";
        }
    }
}

void tst4() {
    environment env;
    substitution subst;
    ho_unifier  unify(env);
    expr N  = Const("N");
    env.add_var("N", Type());
    env.add_var("f", N >> (N >> N));
    expr x  = Const("x");
    expr y  = Const("y");
    expr f  = Const("f");
    expr m1; // = subst.mk_metavar();
    expr m2; // = subst.mk_metavar();
    expr l  = Fun({{x, N}, {y, N}}, Eq(y, f(x, m1)));
    expr r  = Fun({{x, N}, {y, N}}, Eq(m2, f(m1, x)));
    auto sols = unify(context(), l, r, subst);
    lean_assert(length(sols) == 1);
    for (auto sol : sols) {
        std::cout << m1 << " -> " << sol.first.get_subst(m1) << "\n";
        std::cout << m2 << " -> " << sol.first.get_subst(m2) << "\n";
        lean_assert(empty(sol.second));
        lean_assert(beta_reduce(instantiate_metavars(l, sol.first)) ==
                    beta_reduce(instantiate_metavars(r, sol.first)));
    }
}

void tst5() {
    environment env;
    substitution subst;
    ho_unifier  unify(env);
    expr N  = Const("N");
    env.add_var("N", Type());
    env.add_var("f", N >> (N >> N));
    expr f  = Const("f");
    expr m1; // = subst.mk_metavar();
    expr l  = f(f(m1));
    expr r  = f(m1);
    auto sols = unify(context(), l, r, subst);
    lean_assert(length(sols) == 0);
}

void tst6() {
    environment env;
    substitution subst;
    ho_unifier  unify(env);
    expr N  = Const("N");
    env.add_var("N", Type());
    env.add_var("f", N >> (N >> N));
    expr x  = Const("x");
    expr y  = Const("y");
    expr f  = Const("f");
    expr m1; // = subst.mk_metavar();
    expr l  = Fun({x, N}, Fun({y, N}, f(m1, y))(x));
    expr r  = Fun({x, N}, f(x, x));
    auto sols = unify(context(), l, r, subst);
    lean_assert(length(sols) == 2);
    for (auto sol : sols) {
        std::cout << m1 << " -> " << sol.first.get_subst(m1) << "\n";
        std::cout << instantiate_metavars(l, sol.first) << "\n";
        lean_assert(empty(sol.second));
        lean_assert(beta_reduce(instantiate_metavars(l, sol.first)) ==
                    beta_reduce(instantiate_metavars(r, sol.first)));
    }
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    return has_violations() ? 1 : 0;
}
