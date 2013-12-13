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
#include "kernel/normalizer.h"
#include "kernel/instantiate.h"
#include "library/basic_thms.h"
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
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr A1 = menv.mk_metavar();
    expr A2 = menv.mk_metavar();
    expr A3 = menv.mk_metavar();
    expr A4 = menv.mk_metavar();
    expr F  = cons(A1, m1(a), cons(A2, m2(n), cons(A3, m3(b), nil(A4))));
    std::cout << F << "\n";
    std::cout << checker.infer_type(F, context(), &menv, &ucs) << "\n";
    expr int_id = Fun({a, Int}, a);
    expr nat_id = Fun({a, Nat}, a);
    ucs.push_back(mk_choice_constraint(context(), m1, { int_id, mk_int_to_real_fn() }, justification()));
    ucs.push_back(mk_choice_constraint(context(), m2, { nat_id, mk_nat_to_int_fn(), mk_nat_to_real_fn() }, justification()));
    ucs.push_back(mk_choice_constraint(context(), m3, { int_id, mk_int_to_real_fn() }, justification()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    elb.next();
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
    env->add_var("g", Pi({A, Type()}, A >> A));
    expr a = Const("a");
    env->add_var("a", Int);
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr m4 = menv.mk_metavar();
    expr int_id = Fun({a, Int}, a);
    expr nat_id = Fun({a, Nat}, a);
    expr F  = m1(g(m2, m3(a)), m4(nVal(0)));
    std::cout << F << "\n";
    std::cout << checker.infer_type(F, context(), &menv, &ucs) << "\n";
    ucs.push_back(mk_choice_constraint(context(), m1, { mk_nat_le_fn(), mk_int_le_fn(), mk_real_le_fn() }, justification()));
    ucs.push_back(mk_choice_constraint(context(), m3, { int_id, mk_int_to_real_fn() }, justification()));
    ucs.push_back(mk_choice_constraint(context(), m4, { nat_id, mk_nat_to_int_fn(), mk_nat_to_real_fn() }, justification()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    elb.next();
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
    env->add_var("f", Pi({A, Type()}, A >> A));
    expr a = Const("a");
    env->add_var("a", Int);
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
    std::cout << checker.infer_type(F, context(), &menv, &ucs) << "\n";
    ucs.push_back(mk_choice_constraint(context(), m2, { mk_nat_le_fn(), mk_int_le_fn(), mk_real_le_fn() }, justification()));
    ucs.push_back(mk_choice_constraint(context(), m4, { nat_id, mk_nat_to_int_fn(), mk_nat_to_real_fn() }, justification()));
    ucs.push_back(mk_choice_constraint(context(), m5, { int_id, mk_int_to_real_fn() }, justification()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    elb.next();
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
    env->add_var("f", Pi({A, Type()}, A >> A));
    expr a = Const("a");
    expr b = Const("b");
    env->add_var("a", Int);
    env->add_var("b", Real);
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
    std::cout << checker.infer_type(F, context(), &menv, &ucs) << "\n";
    ucs.push_back(mk_choice_constraint(context(), m3, { mk_nat_le_fn(), mk_int_le_fn(), mk_real_le_fn() }, justification()));
    ucs.push_back(mk_choice_constraint(context(), m6, { int_id, mk_int_to_real_fn() }, justification()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    elb.next();
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
    env->add_var("f", Pi({A, Type()}, A >> (A >> A)));
    expr a = Const("a");
    expr b = Const("b");
    env->add_var("a", Int);
    env->add_var("b", Real);
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr m4 = menv.mk_metavar();
    expr x = Const("x");
    expr y = Const("y");
    expr int_id = Fun({a, Int}, a);
    expr F = Fun({{x, m1}, {y, m2}}, f(m3, x, y))(m4(a), b);
    std::cout << F << "\n";
    std::cout << checker.infer_type(F, context(), &menv, &ucs) << "\n";
    ucs.push_back(mk_choice_constraint(context(), m4, { int_id, mk_int_to_real_fn() }, justification()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    elb.next();
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
    env->add_var("f", Int >> (Int >> Int));
    env->add_var("a", Int);
    env->add_var("b", Int);
    env->add_axiom("H1", Eq(f(a, f(a, b)), a));
    env->add_axiom("H2", Eq(a, b));
    expr V = Subst(m1, m2, m3, m4, H1, H2);
    expr expected = Eq(f(a, f(b, b)), a);
    expr given    = checker.infer_type(V, context(), &menv, &ucs);
    ucs.push_back(mk_eq_constraint(context(), expected, given, justification()));
    elaborator elb(env, menv, ucs.size(), ucs.data());
    metavar_env s = elb.next();
    std::cout << instantiate_metavars(V, s) << "\n";
}

#define _ mk_placeholder()

static expr elaborate(expr const & e, environment const & env) {
    metavar_env menv;
    buffer<unification_constraint> ucs;
    type_checker checker(env);
    expr e2 = replace_placeholders_with_metavars(e, menv);
    checker.infer_type(e2, context(), &menv, &ucs);
    elaborator elb(env, menv, ucs.size(), ucs.data());
    metavar_env s = elb.next();
    return instantiate_metavars(e2, s);
}

// Check elaborator success
static void success(expr const & e, expr const & expected, environment const & env) {
    std::cout << "\n" << e << "\n\n";
    expr r = elaborate(e, env);
    std::cout << "\n" << e << "\n------>\n" << r << "\n";
    lean_assert_eq(r, expected);
}

// Check elaborator failure
static void fails(expr const & e, environment const & env) {
    try {
        expr new_e = elaborate(e, env);
        std::cout << "new_e: " << new_e << std::endl;
        lean_unreachable();
    } catch (exception &) {
    }
}

// Check elaborator partial success (i.e., result still contain some metavariables */
static void unsolved(expr const & e, environment const & env) {
    expr r = elaborate(e, env);
    std::cout << "\n" << e << "\n------>\n" << r << "\n";
    lean_assert(has_metavar(r));
}

static void tst7() {
    std::cout << "\nTST 7\n";
    environment env;
    import_all(env);
    expr A = Const("A");
    expr B = Const("B");
    expr F = Const("F");
    expr g = Const("g");
    expr a = Const("a");
    expr Nat  = Const("N");
    expr Real = Const("R");
    env->add_var("N", Type());
    env->add_var("R", Type());
    env->add_var("F", Pi({{A, Type()}, {B, Type()}, {g, A >> B}}, A));
    env->add_var("f", Nat >> Real);
    expr f = Const("f");
    success(F(_, _, f), F(Nat, Real, f), env);
    // fails(F(_, Bool, f), env);
    success(F(_, _, Fun({a, Nat}, a)), F(Nat, Nat, Fun({a, Nat}, a)), env);
}

static void tst8() {
    std::cout << "\nTST 8\n";
    environment env;
    import_all(env);
    expr a  = Const("a");
    expr b  = Const("b");
    expr c  = Const("c");
    expr H1 = Const("H1");
    expr H2 = Const("H2");
    env->add_var("a", Bool);
    env->add_var("b", Bool);
    env->add_var("c", Bool);
    env->add_axiom("H1", Eq(a, b));
    env->add_axiom("H2", Eq(b, c));
    success(Trans(_, _, _, _, H1, H2), Trans(Bool, a, b, c, H1, H2), env);
    success(Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1)),
            Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1)), env);
    success(Symm(_, _, _, Trans(_, _ , _ , _ , Symm(_, _, _, H2), Symm(_, _, _, H1))),
            Symm(Bool, c, a, Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1))), env);
    env->add_axiom("H3", a);
    expr H3 = Const("H3");
    success(EqTIntro(_, EqMP(_, _, Symm(_, _, _, Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1))), H3)),
            EqTIntro(c, EqMP(a, c, Symm(Bool, c, a, Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1))), H3)),
            env);
}

static void tst9() {
    std::cout << "\nTST 9\n";
    environment env;
    import_all(env);
    expr Nat = Const("N");
    env->add_var("N", Type());
    env->add_var("vec", Nat >> Type());
    expr n   = Const("n");
    expr vec = Const("vec");
    env->add_var("f", Pi({n, Nat}, vec(n) >> Nat));
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr H = Const("H");
    expr fact = Const("fact");
    env->add_var("a", Nat);
    env->add_var("b", Nat);
    env->add_definition("fact", Bool, Eq(a, b));
    env->add_axiom("H", fact);
    success(Congr2(_, _, _, _, f, H),
            Congr2(Nat, Fun({n, Nat}, vec(n) >> Nat), a, b, f, H), env);
    env->add_var("g", Pi({n, Nat}, vec(n) >> Nat));
    expr g = Const("g");
    env->add_axiom("H2", Eq(f, g));
    expr H2 = Const("H2");
    success(Congr(_, _, _, _, _, _, H2, H),
            Congr(Nat, Fun({n, Nat}, vec(n) >> Nat), f, g, a, b, H2, H), env);
    success(Congr(_, _, _, _, _, _, Refl(_, f), H),
            Congr(Nat, Fun({n, Nat}, vec(n) >> Nat), f, f, a, b, Refl(Pi({n, Nat}, vec(n) >> Nat), f), H), env);
    success(Refl(_, a), Refl(Nat, a), env);
}

static void tst10() {
    std::cout << "\nTST 10\n";
    environment env;
    import_all(env);
    expr Nat = Const("N");
    env->add_var("N", Type());
    expr R   = Const("R");
    env->add_var("R", Type());
    env->add_var("a", Nat);
    expr a   = Const("a");
    expr f   = Const("f");
    env->add_var("f", Nat >> ((R >> Nat) >> R));
    expr x   = Const("x");
    expr y   = Const("y");
    expr z   = Const("z");
    success(Fun({{x, _}, {y, _}}, f(x, y)),
            Fun({{x, Nat}, {y, R >> Nat}}, f(x, y)), env);
    success(Fun({{x, _}, {y, _}, {z, _}}, Eq(f(x, y), f(x, z))),
            Fun({{x, Nat}, {y, R >> Nat}, {z, R >> Nat}}, Eq(f(x, y), f(x, z))), env);
    expr A   = Const("A");
    success(Fun({{A, Type()}, {x, _}, {y, _}, {z, _}}, Eq(f(x, y), f(x, z))),
            Fun({{A, Type()}, {x, Nat}, {y, R >> Nat}, {z, R >> Nat}}, Eq(f(x, y), f(x, z))), env);
}

static void tst11() {
    std::cout << "\nTST 11\n";
    environment env;
    import_all(env);
    expr A = Const("A");
    expr B = Const("B");
    expr a = Const("a");
    expr b = Const("b");
    expr f = Const("f");
    expr g = Const("g");
    expr Nat = Const("N");
    env->add_var("N", Type());
    env->add_var("f", Pi({{A, Type()}, {a, A}, {b, A}}, A));
    env->add_var("g", Nat >> Nat);
    success(Fun({{a, _}, {b, _}}, g(f(_, a, b))),
            Fun({{a, Nat}, {b, Nat}}, g(f(Nat, a, b))), env);
}

static void tst12() {
    std::cout << "\nTST 12\n";
    environment env;
    import_all(env);
    expr lst  = Const("list");
    expr nil  = Const("nil");
    expr cons = Const("cons");
    expr N    = Const("N");
    expr A    = Const("A");
    expr f    = Const("f");
    expr l    = Const("l");
    expr a    = Const("a");
    env->add_var("N", Type());
    env->add_var("list", Type() >> Type());
    env->add_var("nil", Pi({A, Type()}, lst(A)));
    env->add_var("cons", Pi({{A, Type()}, {a, A}, {l, lst(A)}}, lst(A)));
    env->add_var("f", lst(N >> N) >> Bool);
    success(Fun({a, _}, f(cons(_, a, cons(_, a, nil(_))))),
            Fun({a, N >> N}, f(cons(N >> N, a, cons(N >> N, a, nil(N >> N))))), env);
}

static void tst13() {
    std::cout << "\nTST 13\n";
    environment env;
    import_all(env);
    expr B = Const("B");
    expr A = Const("A");
    expr x = Const("x");
    expr f = Const("f");
    env->add_var("f", Pi({B, Type()}, B >> B));
    success(Fun({{A, Type()}, {B, Type()}, {x, _}}, f(B, x)),
            Fun({{A, Type()}, {B, Type()}, {x, B}}, f(B, x)), env);
    fails(Fun({{x, _}, {A, Type()}}, f(A, x)), env);
    success(Fun({{A, Type()}, {x, _}}, f(A, x)),
            Fun({{A, Type()}, {x, A}}, f(A, x)), env);
    success(Fun({{A, Type()}, {B, Type()}, {x, _}}, f(A, x)),
            Fun({{A, Type()}, {B, Type()}, {x, A}}, f(A, x)), env);
    success(Fun({{A, Type()}, {B, Type()}, {x, _}}, Eq(f(B, x), f(_, x))),
            Fun({{A, Type()}, {B, Type()}, {x, B}}, Eq(f(B, x), f(B, x))), env);
    success(Fun({{A, Type()}, {B, Type()}, {x, _}}, Eq(f(B, x), f(_, x))),
            Fun({{A, Type()}, {B, Type()}, {x, B}}, Eq(f(B, x), f(B, x))), env);
    unsolved(Fun({{A, _}, {B, _}, {x, _}}, Eq(f(B, x), f(_, x))), env);
}

static void tst14() {
    std::cout << "\nTST 14\n";
    environment env;
    import_all(env);
    expr A = Const("A");
    expr B = Const("B");
    expr f = Const("f");
    expr g = Const("g");
    expr x = Const("x");
    expr y = Const("y");
    env->add_var("N", Type());
    env->add_var("f", Pi({A, Type()}, A >> A));
    expr N = Const("N");
    success(Fun({g, Pi({A, Type()}, A >> (A >> Bool))}, g(_, True, False)),
            Fun({g, Pi({A, Type()}, A >> (A >> Bool))}, g(Bool, True, False)),
            env);
    success(Fun({g, Pi({A, TypeU}, A >> (A >> Bool))}, g(_, Bool, Bool)),
            Fun({g, Pi({A, TypeU}, A >> (A >> Bool))}, g(Type(), Bool, Bool)),
            env);
    success(Fun({g, Pi({A, TypeU}, A >> (A >> Bool))}, g(_, Bool, N)),
            Fun({g, Pi({A, TypeU}, A >> (A >> Bool))}, g(Type(), Bool, N)),
            env);
    success(Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g(_,
                  Fun({{x, _}, {y, _}}, Eq(f(_, x), f(_, y))),
                  Fun({{x, N}, {y, Bool}}, True))),
            Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g((N >> (Bool >> Bool)),
                  Fun({{x, N}, {y, Bool}}, Eq(f(N, x), f(Bool, y))),
                  Fun({{x, N}, {y, Bool}}, True))), env);

    success(Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g(_,
                  Fun({{x, N}, {y, _}}, Eq(f(_, x), f(_, y))),
                  Fun({{x, _}, {y, Bool}}, True))),
            Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g((N >> (Bool >> Bool)),
                  Fun({{x, N}, {y, Bool}}, Eq(f(N, x), f(Bool, y))),
                  Fun({{x, N}, {y, Bool}}, True))), env);
}

static void tst15() {
    std::cout << "\nTST 15\n";
    environment env;
    import_all(env);
    expr A = Const("A");
    expr B = Const("B");
    expr C = Const("C");
    expr a = Const("a");
    expr b = Const("b");
    expr eq = Const("my_eq");
    env->add_var("my_eq", Pi({A, Type()}, A >> (A >> Bool)));
    success(Fun({{A, Type()}, {B, Type()}, {a, _}, {b, B}}, eq(_, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, B}, {b, B}}, eq(B, a, b)), env);
    success(Fun({{A, Type()}, {B, Type()}, {a, _}, {b, A}}, eq(_, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, A}, {b, A}}, eq(A, a, b)), env);
    success(Fun({{A, Type()}, {B, Type()}, {a, A}, {b, _}}, eq(_, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, A}, {b, A}}, eq(A, a, b)), env);
    success(Fun({{A, Type()}, {B, Type()}, {a, B}, {b, _}}, eq(_, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, B}, {b, B}}, eq(B, a, b)), env);
    success(Fun({{A, Type()}, {B, Type()}, {a, B}, {b, _}, {C, Type()}}, eq(_, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, B}, {b, B}, {C, Type()}}, eq(B, a, b)), env);
    fails(Fun({{A, Type()}, {B, Type()}, {a, _}, {b, _}, {C, Type()}}, eq(C, a, b)), env);
    success(Fun({{A, Type()}, {B, Type()}, {a, _}, {b, _}, {C, Type()}}, eq(B, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, B}, {b, B}, {C, Type()}}, eq(B, a, b)), env);
}

static void tst16() {
    std::cout << "\nTST 16\n";
    environment env;
    import_all(env);
    expr a  = Const("a");
    expr b  = Const("b");
    expr c  = Const("c");
    expr H1 = Const("H1");
    expr H2 = Const("H2");
    env->add_var("a", Bool);
    env->add_var("b", Bool);
    env->add_var("c", Bool);
    success(Fun({{H1, Eq(a, b)}, {H2, Eq(b, c)}},
                Trans(_, _, _, _, H1, H2)),
            Fun({{H1, Eq(a, b)}, {H2, Eq(b, c)}},
                Trans(Bool, a, b, c, H1, H2)),
            env);
    expr H3 = Const("H3");
    success(Fun({{H1, Eq(a, b)}, {H2, Eq(b, c)}, {H3, a}},
                EqTIntro(_, EqMP(_, _, Symm(_, _, _, Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1))), H3))),
            Fun({{H1, Eq(a, b)}, {H2, Eq(b, c)}, {H3, a}},
                EqTIntro(c, EqMP(a, c, Symm(Bool, c, a, Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1))), H3))),
            env);
    environment env2;
    import_all(env2);
    success(Fun({{a, Bool}, {b, Bool}, {c, Bool}, {H1, Eq(a, b)}, {H2, Eq(b, c)}, {H3, a}},
                EqTIntro(_, EqMP(_, _, Symm(_, _, _, Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1))), H3))),
            Fun({{a, Bool}, {b, Bool}, {c, Bool}, {H1, Eq(a, b)}, {H2, Eq(b, c)}, {H3, a}},
                EqTIntro(c, EqMP(a, c, Symm(Bool, c, a, Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1))), H3))),
            env2);
    expr A = Const("A");
    success(Fun({{A, Type()}, {a, A}, {b, A}, {c, A}, {H1, Eq(a, b)}, {H2, Eq(b, c)}},
                Symm(_, _, _, Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1)))),
            Fun({{A, Type()}, {a, A}, {b, A}, {c, A}, {H1, Eq(a, b)}, {H2, Eq(b, c)}},
                Symm(A, c, a, Trans(A, c, b, a, Symm(A, b, c, H2), Symm(A, a, b, H1)))),
            env2);
}

void tst17() {
    std::cout << "\nTST 17\n";
    environment env;
    import_all(env);
    expr A  = Const("A");
    expr B  = Const("B");
    expr a  = Const("a");
    expr b  = Const("b");
    expr eq = Const("my_eq");
    env->add_var("my_eq", Pi({A, Type(level()+1)}, A >> (A >> Bool)));
    success(eq(_, Fun({{A, Type()}, {a, _}}, a), Fun({{B, Type()}, {b, B}}, b)),
            eq(Pi({A, Type()}, A >> A), Fun({{A, Type()}, {a, A}}, a), Fun({{B, Type()}, {b, B}}, b)),
            env);
}

void tst18() {
    std::cout << "\nTST 18\n";
    environment env;
    import_all(env);
    expr A  = Const("A");
    expr h  = Const("h");
    expr f  = Const("f");
    expr a  = Const("a");
    env->add_var("h", Pi({A, Type()}, A) >> Bool);
    success(Fun({{f, Pi({A, Type()}, _)}, {a, Bool}}, h(f)),
            Fun({{f, Pi({A, Type()}, A)}, {a, Bool}}, h(f)),
            env);
}

void tst19() {
    std::cout << "\nTST 19\n";
    environment env;
    import_all(env);
    expr R  = Const("R");
    expr A  = Const("A");
    expr r  = Const("r");
    expr eq = Const("my_eq");
    expr f  = Const("f");
    expr g  = Const("g");
    expr h  = Const("h");
    expr D  = Const("D");
    env->add_var("R", Type() >> Bool);
    env->add_var("r", Pi({A, Type()}, R(A)));
    env->add_var("h", Pi({A, Type()}, R(A)) >> Bool);
    env->add_var("my_eq", Pi({A, Type(level()+1)}, A >> (A >> Bool)));
    success(Let({{f, Fun({A, Type()}, r(_))},
                 {g, Fun({A, Type()}, r(_))},
                 {D, Fun({A, Type()}, eq(_, f(A), g(_)))}},
                h(f)),
            Let({{f, Fun({A, Type()}, r(A))},
                 {g, Fun({A, Type()}, r(A))},
                 {D, Fun({A, Type()}, eq(R(A), f(A), g(A)))}},
                h(f)),
            env);
}

void tst20() {
    std::cout << "\nTST 20\n";
    environment env;
    metavar_env menv;
    expr N  = Const("N");
    expr M  = Const("M");
    env->add_var("N", Type());
    env->add_var("M", Type());
    env->add_var("f", N >> (M >> M));
    env->add_var("a", N);
    env->add_var("b", M);
    expr f  = Const("f");
    expr x  = Const("x");
    expr a  = Const("a");
    expr b  = Const("b");
    expr m1 = menv.mk_metavar();
    expr l = m1(b, a);
    expr r = f(b, f(a, b));
    elaborator elb(env, menv, context(), l, r);
    while (true) {
        try {
            auto sol = elb.next();
            std::cout << m1 << " -> " << *(sol.get_subst(m1)) << "\n";
            std::cout << instantiate_metavars(l, sol) << "\n";
            lean_assert(instantiate_metavars(l, sol) == r);
            std::cout << "--------------\n";
        } catch (elaborator_exception & ex) {
            break;
        }
    }
}

void tst21() {
    std::cout << "\nTST 21\n";
    environment env;
    import_all(env);
    metavar_env menv;
    expr N  = Const("N");
    expr M  = Const("M");
    env->add_var("N", Type());
    env->add_var("f", N >> (Bool >> N));
    env->add_var("a", N);
    env->add_var("b", N);
    expr f  = Const("f");
    expr x  = Const("x");
    expr a  = Const("a");
    expr b  = Const("b");
    expr m1 = menv.mk_metavar();
    expr l = m1(b, a);
    expr r = Fun({x, N}, f(x, Eq(a, b)));
    elaborator elb(env, menv, context(), l, r);
    while (true) {
        try {
            auto sol = elb.next();
            std::cout << m1 << " -> " << *(sol.get_subst(m1)) << "\n";
            std::cout << instantiate_metavars(l, sol) << "\n";
            lean_assert(instantiate_metavars(l, sol) == r);
            std::cout << "--------------\n";
        } catch (elaborator_exception & ex) {
            break;
        }
    }
}

void tst22() {
    std::cout << "\nTST 22\n";
    environment env;
    import_all(env);
    metavar_env menv;
    expr N  = Const("N");
    env->add_var("N", Type());
    env->add_var("f", N >> (Int >> N));
    env->add_var("a", N);
    env->add_var("b", N);
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr t1 = menv.get_type(m1);
    expr t2 = menv.get_type(m2);
    expr f  = Const("f");
    expr a  = Const("a");
    expr b  = Const("b");
    expr l = f(m1(a), iAdd(m3, iAdd(iVal(1), iVal(1))));
    expr r = f(m2(b), iAdd(iVal(1), iVal(2)));
    elaborator elb(env, menv, context(), l, r);
    while (true) {
        try {
            auto sol = elb.next();
            std::cout << m3 << " -> " << *(sol.get_subst(m3)) << "\n";
            lean_assert(*(sol.get_subst(m3)) == iVal(1));
            std::cout << instantiate_metavars(l, sol) << "\n";
            std::cout << instantiate_metavars(r, sol) << "\n";
            std::cout << "--------------\n";
        } catch (elaborator_exception & ex) {
            break;
        }
    }
}

void tst23() {
    std::cout << "\nTST 23\n";
    environment env;
    import_all(env);
    metavar_env menv;
    expr N  = Const("N");
    env->add_var("N", Type());
    env->add_var("f", N >> (N >> N));
    expr x  = Const("x");
    expr y  = Const("y");
    expr f  = Const("f");
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr l  = Fun({{x, N}, {y, N}}, Eq(y, f(x, m1)));
    expr r  = Fun({{x, N}, {y, N}}, Eq(m2, f(m1, x)));
    elaborator elb(env, menv, context(), l, r);
    while (true) {
        try {
            auto sol = elb.next();
            std::cout << m1 << " -> " << *(sol.get_subst(m1)) << "\n";
            std::cout << instantiate_metavars(l, sol) << "\n";
            lean_assert_eq(instantiate_metavars(l, sol),
                           instantiate_metavars(r, sol));
            std::cout << "--------------\n";
        } catch (elaborator_exception & ex) {
            break;
        }
    }
}

void tst24() {
    std::cout << "\nTST 24\n";
    environment env;
    import_all(env);
    metavar_env menv;
    expr N  = Const("N");
    env->add_var("N", Type());
    env->add_var("f", N >> (N >> N));
    expr f  = Const("f");
    expr m1 = menv.mk_metavar();
    expr l  = f(f(m1));
    expr r  = f(m1);
    elaborator elb(env, menv, context(), l, r);
    try {
        elb.next();
        lean_unreachable();
    } catch (elaborator_exception & ex) {
    }
}

void tst25() {
    std::cout << "\nTST 25\n";
    environment env;
    import_all(env);
    metavar_env menv;
    expr N  = Const("N");
    env->add_var("N", Type());
    env->add_var("f", N >> (N >> N));
    expr x  = Const("x");
    expr y  = Const("y");
    expr f  = Const("f");
    expr m1 = menv.mk_metavar();
    expr l  = Fun({x, N}, Fun({y, N}, f(m1, y))(x));
    expr r  = Fun({x, N}, f(x, x));
    elaborator elb(env, menv, context(), l, r);
    while (true) {
        try {
            auto sol = elb.next();
            std::cout << m1 << " -> " << *(sol.get_subst(m1)) << "\n";
            std::cout << instantiate_metavars(l, sol) << "\n";
            lean_assert_eq(beta_reduce(instantiate_metavars(l, sol)),
                           beta_reduce(instantiate_metavars(r, sol)));
            std::cout << "--------------\n";
        } catch (elaborator_exception & ex) {
            break;
        }
    }
}

void tst26() {
    std::cout << "\nTST 26\n";
    /*
      Solve elaboration problem for

      g : Pi (A : Type U), A -> A
      a : Type 1
      Axiom H : g _ a = a
    */
    environment env;
    import_all(env);
    metavar_env menv;
    buffer<unification_constraint> ucs;
    type_checker checker(env);
    expr A = Const("A");
    expr g = Const("g");
    env->add_var("g", Pi({A, TypeU}, A >> A));
    expr a = Const("a");
    env->add_var("a", Type(level()+1));
    expr m1 = menv.mk_metavar();
    expr F  = Eq(g(m1, a), a);
    std::cout << F << "\n";
    std::cout << checker.infer_type(F, context(), &menv, &ucs) << "\n";
    elaborator elb(env, menv, ucs.size(), ucs.data());
    metavar_env s = elb.next();
    std::cout << instantiate_metavars(F, s) << "\n";
    lean_assert_eq(instantiate_metavars(F, s), Eq(g(Type(level()+1), a), a));
}

void tst27() {
    std::cout << "\nTST 27\n";
    /*
      Solve elaboration problem for

      g : Pi (A : Type U), A -> A
      eq : Pi (A : Type U), A -> A -> Bool
      a : Type M
      fun f : _, eq _ ((g _ f) a) a
    */
    environment env;
    import_all(env);
    metavar_env menv;
    buffer<unification_constraint> ucs;
    type_checker checker(env);
    expr A = Const("A");
    expr g = Const("g");
    expr f = Const("f");
    expr a = Const("a");
    expr eq = Const("my_eq");
    env->add_var("my_eq", Pi({A, TypeU}, A >> (A >> Bool)));
    env->add_var("g", Pi({A, TypeU}, A >> A));
    env->add_var("a", TypeM);
    expr m1 = menv.mk_metavar();
    expr m2 = menv.mk_metavar();
    expr m3 = menv.mk_metavar();
    expr F  = Fun({f, m1}, eq(m2, g(m3, f)(a), a));
    std::cout << F << "\n";
    std::cout << checker.infer_type(F, context(), &menv, &ucs) << "\n";
    elaborator elb(env, menv, ucs.size(), ucs.data());
    metavar_env s = elb.next();
    std::cout << instantiate_metavars(F, s) << "\n";
    lean_assert_eq(instantiate_metavars(F, s),
                   Fun({f, TypeM >> TypeM}, eq(TypeM, g(TypeM >> TypeM, f)(a), a)));
}

int main() {
    save_stack_info();
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
    tst26();
    tst27();
    return has_violations() ? 1 : 0;
}
