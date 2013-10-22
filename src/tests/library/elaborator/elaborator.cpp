/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/kernel_exception.h"
#include "library/basic_thms.h"
#include "library/reduce.h"
#include "library/placeholder.h"
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
    std::cout << beta_reduce(instantiate_metavars(V, s)) << "\n";
}

#define _ mk_placholder()

static expr elaborate(expr const & e, environment const & env) {
    metavar_env menv;
    buffer<unification_constraint> ucs;
    type_checker checker(env);
    expr e2 = replace_placeholders_with_metavars(e, menv);
    checker.infer_type(e2, context(), &menv, ucs);
    elaborator elb(env, menv, ucs.size(), ucs.data());
    substitution s = elb.next();
    return beta_reduce(instantiate_metavars(e2, s));
}

// Check elaborator success
static void success(expr const & e, expr const & expected, environment const & env) {
    std::cout << "\n" << e << "\n------>\n";
    expr r = elaborate(e, env);
    std::cout << r << "\n";
    lean_assert(r == expected);
}

static void tst7() {
    environment env;
    import_all(env);
    expr A = Const("A");
    expr B = Const("B");
    expr F = Const("F");
    expr g = Const("g");
    expr a = Const("a");
    expr Nat  = Const("N");
    expr Real = Const("R");
    env.add_var("N", Type());
    env.add_var("R", Type());
    env.add_var("F", Pi({{A, Type()}, {B, Type()}, {g, A >> B}}, A));
    env.add_var("f", Nat >> Real);
    expr f = Const("f");
    success(F(_, _, f), F(Nat, Real, f), env);
    // fails(F(_, Bool, f), env);
    success(F(_, _, Fun({a, Nat}, a)), F(Nat, Nat, Fun({a, Nat}, a)), env);
}

static void tst8() {
    environment env;
    import_all(env);
    expr a  = Const("a");
    expr b  = Const("b");
    expr c  = Const("c");
    expr H1 = Const("H1");
    expr H2 = Const("H2");
    env.add_var("a", Bool);
    env.add_var("b", Bool);
    env.add_var("c", Bool);
    env.add_axiom("H1", Eq(a, b));
    env.add_axiom("H2", Eq(b, c));
    success(Trans(_, _, _, _, H1, H2), Trans(Bool, a, b, c, H1, H2), env);
    success(Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1)),
            Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1)), env);
    success(Symm(_, _, _, Trans(_, _ , _ , _ , Symm(_, _, _, H2), Symm(_, _, _, H1))),
            Symm(Bool, c, a, Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1))), env);
    env.add_axiom("H3", a);
    expr H3 = Const("H3");
    success(EqTIntro(_, EqMP(_, _, Symm(_, _, _, Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1))), H3)),
            EqTIntro(c, EqMP(a, c, Symm(Bool, c, a, Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1))), H3)),
            env);
}

static void tst9() {
    environment env;
    import_all(env);
    expr Nat = Const("N");
    env.add_var("N", Type());
    env.add_var("vec", Nat >> Type());
    expr n   = Const("n");
    expr vec = Const("vec");
    env.add_var("f", Pi({n, Nat}, vec(n) >> Nat));
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr H = Const("H");
    expr fact = Const("fact");
    env.add_var("a", Nat);
    env.add_var("b", Nat);
    env.add_definition("fact", Bool, Eq(a, b));
    env.add_axiom("H", fact);
    success(Congr2(_, _, _, _, f, H),
            Congr2(Nat, Fun({n, Nat}, vec(n) >> Nat), a, b, f, H), env);
    env.add_var("g", Pi({n, Nat}, vec(n) >> Nat));
    expr g = Const("g");
    env.add_axiom("H2", Eq(f, g));
    expr H2 = Const("H2");
    success(Congr(_, _, _, _, _, _, H2, H),
            Congr(Nat, Fun({n, Nat}, vec(n) >> Nat), f, g, a, b, H2, H), env);
    success(Congr(_, _, _, _, _, _, Refl(_, f), H),
            Congr(Nat, Fun({n, Nat}, vec(n) >> Nat), f, f, a, b, Refl(Pi({n, Nat}, vec(n) >> Nat), f), H), env);
    success(Refl(_, a), Refl(Nat, a), env);
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
    return has_violations() ? 1 : 0;
}

