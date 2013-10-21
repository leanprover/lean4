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

static void tst2() {
    /*
      Solve elaboration problem for

      g : Pi (A : Type), A -> A
      a : Int
      Axiom H : g _ a <= 0

      The following elaboration problem is created

         ?m1 (g ?m2 (?m3 a)) (?m4 a)

         ?m1 in { Nat::Le, Int::Le, Real::Le }
         ?m3 in { Id, int2real }
         ?m4 in { Id, nat2int, nat2real }
    */
    environment env;
    import_all(env);
    metavar_env menv;
    buffer<unification_constraint> ucs;
    type_checker checker(env);
    expr A = Const("A");
    expr g = Const("g");
    env.add_var("g", Pi({A, Type()}, A >> A));
    expr a = Const("a");
    env.add_var("a", Int);
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr m4 = menv.mk_metavar();
    expr int_id = Fun({a, Int}, a);
    expr nat_id = Fun({a, Nat}, a);
    expr F  = m1(g(m2, m3(a)), m4(nVal(0)));
    std::cout << F << "\n";
    std::cout << checker.infer_type(F, context(), &menv, ucs) << "\n";
    ucs.push_back(mk_choice_constraint(context(), m1, { mk_nat_le_fn(), mk_int_le_fn(), mk_real_le_fn() }, trace()));
    ucs.push_back(mk_choice_constraint(context(), m3, { int_id, mk_int_to_real_fn() }, trace()));
    ucs.push_back(mk_choice_constraint(context(), m4, { nat_id, mk_nat_to_int_fn(), mk_nat_to_real_fn() }, trace()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    substitution s = elb.next();
}

static void tst3() {
    /*
      Solve elaboration problem for

      a : Int
      (fun x, (f x) > 10) a

      The following elaboration problem is created

        (fun x : ?m1, ?m2 (f ?m3 x) (?m4 10)) (?m5 a)

        ?m2 in { Nat::Le, Int::Le, Real::Le }
        ?m4 in { Id, nat2int, nat2real }
        ?m5 in { Id, int2real }
    */
    environment env;
    import_all(env);
    metavar_env menv;
    buffer<unification_constraint> ucs;
    type_checker checker(env);
    expr A = Const("A");
    expr f = Const("f");
    env.add_var("f", Pi({A, Type()}, A >> A));
    expr a = Const("a");
    env.add_var("a", Int);
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr m4 = menv.mk_metavar();
    expr m5 = menv.mk_metavar();
    expr int_id = Fun({a, Int}, a);
    expr nat_id = Fun({a, Nat}, a);
    expr x = Const("x");
    expr F = Fun({x, m1}, m2(f(m3, x), m4(nVal(10))))(m5(a));
    std::cout << F << "\n";
    std::cout << checker.infer_type(F, context(), &menv, ucs) << "\n";
    ucs.push_back(mk_choice_constraint(context(), m2, { mk_nat_le_fn(), mk_int_le_fn(), mk_real_le_fn() }, trace()));
    ucs.push_back(mk_choice_constraint(context(), m4, { nat_id, mk_nat_to_int_fn(), mk_nat_to_real_fn() }, trace()));
    ucs.push_back(mk_choice_constraint(context(), m5, { int_id, mk_int_to_real_fn() }, trace()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    substitution s = elb.next();
}

static void tst4() {
    /*
      Variable f {A : Type} (a : A) : A
      Variable a : Int
      Variable b : Real
      (fun x y, (f x) > (f y)) a b

      The following elaboration problem is created

           (fun (x : ?m1) (y : ?m2), ?m3 (f ?m4 x) (f ?m5 y)) (?m6 a) b

           ?m3 in { Nat::Le, Int::Le, Real::Le }
           ?m6 in { Id, int2real }
    */
    environment env;
    import_all(env);
    metavar_env menv;
    buffer<unification_constraint> ucs;
    type_checker checker(env);
    expr A = Const("A");
    expr f = Const("f");
    env.add_var("f", Pi({A, Type()}, A >> A));
    expr a = Const("a");
    expr b = Const("b");
    env.add_var("a", Int);
    env.add_var("b", Real);
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr m4 = menv.mk_metavar();
    expr m5 = menv.mk_metavar();
    expr m6 = menv.mk_metavar();
    expr x = Const("x");
    expr y = Const("y");
    expr int_id = Fun({a, Int}, a);
    expr F = Fun({{x, m1}, {y, m2}}, m3(f(m4, x), f(m5, y)))(m6(a), b);
    std::cout << F << "\n";
    std::cout << checker.infer_type(F, context(), &menv, ucs) << "\n";
    ucs.push_back(mk_choice_constraint(context(), m3, { mk_nat_le_fn(), mk_int_le_fn(), mk_real_le_fn() }, trace()));
    ucs.push_back(mk_choice_constraint(context(), m6, { int_id, mk_int_to_real_fn() }, trace()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    substitution s = elb.next();
}

static void tst5() {
    /*

      Variable f {A : Type} (a b : A) : Bool
      Variable a : Int
      Variable b : Real
      (fun x y, f x y) a b

      The following elaboration problem is created

           (fun (x : ?m1) (y : ?m2), (f ?m3 x y)) (?m4 a) b

           ?m4 in { Id, int2real }
    */
    environment env;
    import_all(env);
    metavar_env menv;
    buffer<unification_constraint> ucs;
    type_checker checker(env);
    expr A = Const("A");
    expr f = Const("f");
    env.add_var("f", Pi({A, Type()}, A >> (A >> A)));
    expr a = Const("a");
    expr b = Const("b");
    env.add_var("a", Int);
    env.add_var("b", Real);
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr m4 = menv.mk_metavar();
    expr x = Const("x");
    expr y = Const("y");
    expr int_id = Fun({a, Int}, a);
    expr F = Fun({{x, m1}, {y, m2}}, f(m3, x, y))(m4(a), b);
    std::cout << F << "\n";
    std::cout << checker.infer_type(F, context(), &menv, ucs) << "\n";
    ucs.push_back(mk_choice_constraint(context(), m4, { int_id, mk_int_to_real_fn() }, trace()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    substitution s = elb.next();
}

static void tst6() {
    /*
      Subst : Π (A : Type U) (a b : A) (P : A → Bool), (P a) → (a = b) → (P b)
      f : Int -> Int -> Int
      a : Int
      b : Int
      H1 : (f a (f a b)) == a
      H2 : a = b
      Theorem T : (f a (f b b)) == a := Subst _ _ _ _ H1 H2
    */
    environment env;
    import_all(env);
    metavar_env menv;
    buffer<unification_constraint> ucs;
    type_checker checker(env);
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr H1 = Const("H1");
    expr H2 = Const("H2");
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr m4 = menv.mk_metavar();
    env.add_var("f", Int >> (Int >> Int));
    env.add_var("a", Int);
    env.add_var("b", Int);
    env.add_axiom("H1", Eq(f(a, f(a, b)), a));
    env.add_axiom("H2", Eq(a, b));
    expr V = Subst(m1, m2, m3, m4, H1, H2);
    expr expected = Eq(f(a, f(b, b)), a);
    expr given    = checker.infer_type(V, context(), &menv, ucs);
    ucs.push_back(mk_eq_constraint(context(), expected, given, trace()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    substitution s = elb.next();
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

