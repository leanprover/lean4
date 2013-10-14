/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "library/arith/arith.h"
#include "library/all/all.h"
#include "library/elaborator/elaborator.h"
using namespace lean;

static void tst1() {
    environment env;
    import_all(env);
    metavar_env menv;
    buffer<unification_constraint> ucs;
    type_checker checker(env);
    expr list = Const("list");
    expr nil  = Const("nil");
    expr cons = Const("cons");
    expr A    = Const("A");
    env.add_var("list", Type() >> Type());
    env.add_var("nil", Pi({A, Type()}, list(A)));
    env.add_var("cons", Pi({A, Type()}, A >> (list(A) >> list(A))));
    env.add_var("a", Int);
    env.add_var("b", Int);
    env.add_var("n", Nat);
    env.add_var("m", Nat);
    expr a  = Const("a");
    expr b  = Const("b");
    expr n  = Const("n");
    expr m  = Const("m");
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr A1 = menv.mk_metavar();
    expr A2 = menv.mk_metavar();
    expr A3 = menv.mk_metavar();
    expr A4 = menv.mk_metavar();
    expr F  = cons(A1, m1(a), cons(A2, m2(n), cons(A3, m3(b), nil(A4))));
    std::cout << F << "\n";
    std::cout << checker.infer_type(F, context(), &menv, ucs) << "\n";
    expr int_id = Fun({a, Int}, a);
    expr nat_id = Fun({a, Nat}, a);
    ucs.push_back(mk_choice_constraint(context(), m1, { int_id, mk_int_to_real_fn() }, trace()));
    ucs.push_back(mk_choice_constraint(context(), m2, { nat_id, mk_nat_to_int_fn(), mk_nat_to_real_fn() }, trace()));
    ucs.push_back(mk_choice_constraint(context(), m3, { int_id, mk_int_to_real_fn() }, trace()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    substitution s = elb.next();
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}

