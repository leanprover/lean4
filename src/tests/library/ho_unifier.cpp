/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/environment.h"
#include "library/ho_unifier.h"
#include "library/printer.h"
#include "library/reduce.h"
using namespace lean;

void tst1() {
    environment env;
    metavar_env menv;
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
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr l = m1(b, a);
    expr r = f(b, f(a, b));
    for (auto sol : unify(context(), l, r, menv)) {
        std::cout << m1 << " -> " << beta_reduce(sol.first.get_subst(m1)) << "\n";
        std::cout << beta_reduce(instantiate_metavars(l, sol.first)) << "\n";
        lean_assert(beta_reduce(instantiate_metavars(l, sol.first)) == r);
        std::cout << "--------------\n";
    }
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}
