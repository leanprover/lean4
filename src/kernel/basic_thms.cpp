/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "basic_thms.h"
#include "environment.h"
#include "abstract.h"
#include "type_check.h"

namespace lean {

MK_CONSTANT(true_neq_false,    name("TrueNeFalse"));
MK_CONSTANT(truth,             name("Truth"));
MK_CONSTANT(false_elim_fn,     name("FalseElim"));
MK_CONSTANT(absurd_fn,         name("Absurd"));
MK_CONSTANT(em_fn,             name("EM"));
MK_CONSTANT(double_neg_fn,     name("DoubleNeg"));
MK_CONSTANT(mt_fn,             name("MT"));
MK_CONSTANT(contrapos_fn,      name("Contrapos"));
MK_CONSTANT(conj_fn,           name("Conj"));
MK_CONSTANT(symm_fn,           name("Symm"));
MK_CONSTANT(trans_fn,          name("Trans"));
MK_CONSTANT(xtrans_fn,         name("xTrans"));
MK_CONSTANT(congr1_fn,         name("Congr1"));
MK_CONSTANT(congr2_fn,         name("Congr2"));
MK_CONSTANT(congr_fn,          name("Congr"));
MK_CONSTANT(eq_mp_fn,          name("EqMP"));
MK_CONSTANT(eqt_elim_fn,       name("EqTElim"));
MK_CONSTANT(forall_elim_fn,    name("ForallElim"));

#if 0
MK_CONSTANT(ext_fn,            name("ext"));
MK_CONSTANT(foralli_fn,        name("foralli"));
MK_CONSTANT(domain_inj_fn,     name("domain_inj"));
MK_CONSTANT(range_inj_fn,      name("range_inj"));
#endif

void add_basic_thms(environment & env) {
    expr A  = Const("A");
    expr a  = Const("a");
    expr b  = Const("b");
    expr c  = Const("c");
    expr H  = Const("H");
    expr H1 = Const("H1");
    expr H2 = Const("H2");
    expr B  = Const("B");
    expr f  = Const("f");
    expr g  = Const("g");
    expr h  = Const("h");
    expr x  = Const("x");
    expr y  = Const("y");
    expr z  = Const("z");
    expr P  = Const("P");
    expr A1 = Const("A1");
    expr B1 = Const("B1");
    expr a1 = Const("a1");

    expr A_pred    = A >> Bool;
    expr q_type    = Pi({A, TypeU}, A_pred >> Bool);
    expr piABx     = Pi({x, A}, B(x));
    expr A_arrow_u = A >> TypeU;

    // True_neq_False : Not(True = False)
    env.add_theorem(true_neq_false_name, Not(Eq(True, False)), Trivial);

    // Truth : True := Trivial
    env.add_theorem(truth_name, True, Trivial);

    // FalseElim : Pi (a : Bool) (H : False), a
    env.add_theorem(false_elim_fn_name, Pi({{a, Bool}, {H, False}}, a),
                    Fun({{a, Bool}, {H, False}}, Case(Fun({x, Bool}, x), Truth, H, a)));

    // Absurd : Pi (a : Bool) (H1 : a) (H2 : Not a), False
    env.add_theorem(absurd_fn_name, Pi({{a, Bool}, {H1, a}, {H2, Not(a)}}, False),
                    Fun({{a, Bool}, {H1, a}, {H2, Not(a)}},
                        MP(a, False, H2, H1)));

    // DoubleNeg : Pi (a : Bool), Eq(Not(Not(a)), a)
    env.add_theorem(double_neg_fn_name, Pi({a, Bool}, Eq(Not(Not(a)), a)),
                    Fun({a, Bool}, Case(Fun({x, Bool}, Eq(Not(Not(x)), x)), Trivial, Trivial, a)));

    // ModusTollens : Pi (a b : Bool) (H1 : a => b) (H2 : Not(b)), Not(a)
    env.add_theorem(mt_fn_name, Pi({{a, Bool}, {b, Bool}, {H1, Implies(a, b)}, {H2, Not(b)}}, Not(a)),
                    Fun({{a, Bool}, {b, Bool}, {H1, Implies(a, b)}, {H2, Not(b)}},
                        Discharge(a, False, Fun({H, a},
                                                Absurd(b, MP(a, b, H1, H), H2)))));

    // Contrapositive : Pi (a b : Bool) (H : a => b), (Not(b) => Not(a))
    env.add_theorem(contrapos_fn_name, Pi({{a, Bool}, {b, Bool}, {H, Implies(a, b)}}, Implies(Not(b), Not(a))),
                    Fun({{a, Bool}, {b, Bool}, {H, Implies(a, b)}},
                        Discharge(Not(b), Not(a), Fun({H1, Not(b)}, MT(a, b, H, H1)))));

    // Conj : Pi (a b : Bool) (H1 : a) (H2 : b), And(a, b)
    env.add_theorem(conj_fn_name, Pi({{a, Bool}, {b, Bool}, {H1, a}, {H2, b}}, And(a, b)),
                    Fun({{a, Bool}, {b, Bool}, {H1, a}, {H2, b}},
                        Discharge(Implies(a, Not(b)), False, Fun({H, Implies(a, Not(b))},
                                                                 Absurd(b, H2, MP(a, Not(b), H, H1))))));

    // Iff : Pi (a b : Bool) (H1 : a => b) (H2 : b => a), a = b

    // Symm : Pi (A : Type u) (a b : A) (H : a = b), b = a :=
    //         Subst A (Fun x : A => x = a) a b (Refl A a) H
    env.add_theorem(symm_fn_name, Pi({{A, TypeU}, {a, A}, {b, A}, {H, Eq(a, b)}}, Eq(b, a)),
                    Fun({{A, TypeU}, {a, A}, {b, A}, {H, Eq(a, b)}},
                        Subst(A, Fun({x, A}, Eq(x,a)), a, b, Refl(A, a), H)));

    // Trans: Pi (A: Type u) (a b c : A) (H1 : a = b) (H2 : b = c), a = c :=
    //           Subst A (Fun x : A => a = x) b c H1 H2
    env.add_theorem(trans_fn_name, Pi({{A, TypeU}, {a, A}, {b, A}, {c, A}, {H1, Eq(a, b)}, {H2, Eq(b, c)}}, Eq(a, c)),
                    Fun({{A, TypeU}, {a, A}, {b, A}, {c, A}, {H1, Eq(a,b)}, {H2, Eq(b,c)}},
                        Subst(A, Fun({x, A}, Eq(a, x)), b, c, H1, H2)));

    // xTrans: Pi (A: Type u) (B : Type u) (a : A) (b c : B) (H1 : a = b) (H2 : b = c), a = c :=
    //           Subst B (Fun x : B => a = x) b c H1 H2
    env.add_theorem(xtrans_fn_name, Pi({{A, TypeU}, {B, TypeU}, {a, A}, {b, B}, {c, B}, {H1, Eq(a, b)}, {H2, Eq(b, c)}}, Eq(a, c)),
                    Fun({{A, TypeU}, {B, TypeU}, {a, A}, {b, B}, {c, B}, {H1, Eq(a, b)}, {H2, Eq(b, c)}},
                        Subst(B, Fun({x, B}, Eq(a, x)), b, c, H1, H2)));

    // OrIntro1 : Pi (a b : Bool) (H : a), Or(a, b)
    env.add_theorem(name("OrIntro1"), Pi({{a, Bool}, {b, Bool}, {H, a}}, Or(a, b)),
                    Fun({{a, Bool}, {b, Bool}, {H, a}},
                        Discharge(Not(a), b, Fun({H1, Not(a)},
                                                 FalseElim(b, Absurd(a, H, H1))))));

    // EM : Pi (a : Bool), Or(a, Not(a))
    env.add_theorem(em_fn_name, Pi({a, Bool}, Or(a, Not(a))),
                    Fun({a, Bool}, Case(Fun({x, Bool}, Or(x, Not(x))), Trivial, Trivial, a)));

    env.add_theorem(name("OrIdempotent"), Pi({a, Bool}, Eq(Or(a, a), a)),
                    Fun({a, Bool}, Case(Fun({x, Bool}, Eq(Or(x, x), x)), Trivial, Trivial, a)));

    env.add_theorem(name("OrComm"), Pi({{a, Bool}, {b, Bool}}, Eq(Or(a, b), Or(b, a))),
                    Fun({{a, Bool}, {b, Bool}},
                        Case(Fun({x, Bool}, Eq(Or(x, b), Or(b, x))),
                             Case(Fun({y, Bool}, Eq(Or(True, y),  Or(y, True))),  Trivial, Trivial, b),
                             Case(Fun({y, Bool}, Eq(Or(False, y), Or(y, False))), Trivial, Trivial, b),
                             a)));

    env.add_theorem(name("OrAssoc"), Pi({{a, Bool}, {b, Bool}, {c, Bool}}, Eq(Or(Or(a, b), c), Or(a, Or(b, c)))),
                    Fun({{a, Bool}, {b, Bool}, {c, Bool}},
                        Case(Fun({x, Bool}, Eq(Or(Or(x, b), c), Or(x, Or(b, c)))),
                             Case(Fun({y, Bool}, Eq(Or(Or(True, y), c), Or(True, Or(y, c)))),
                                  Case(Fun({z, Bool}, Eq(Or(Or(True, True), z), Or(True, Or(True, z)))), Trivial, Trivial, c),
                                  Case(Fun({z, Bool}, Eq(Or(Or(True, False), z), Or(True, Or(False, z)))), Trivial, Trivial, c), b),
                             Case(Fun({y, Bool}, Eq(Or(Or(False, y), c), Or(False, Or(y, c)))),
                                  Case(Fun({z, Bool}, Eq(Or(Or(False, True), z), Or(False, Or(True, z)))), Trivial, Trivial, c),
                                  Case(Fun({z, Bool}, Eq(Or(Or(False, False), z), Or(False, Or(False, z)))), Trivial, Trivial, c), b), a)));


    // Congr1 : Pi (A : Type u) (B : A -> Type u) (f g: Pi (x : A) B x) (a : A) (H : f = g), f a = g a :=
    //          Subst piABx (Fun h : piABx => f a = h a) f g (Refl piABx f) H
    env.add_theorem(congr1_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {a, A}, {H, Eq(f, g)}}, Eq(f(a), g(a))),
                    Fun({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {a, A}, {H, Eq(f, g)}},
                        Subst(piABx, Fun({h, piABx}, Eq(f(a), h(a))), f, g, Refl(piABx, f), H)));

    // Congr2 : Pi (A : Type u) (B : A -> Type u) (f : Pi (x : A) B x) (a b : A) (H : a = b), f a = f b :=
    //           Subst A (Fun x : A => f a = f x) a b (Refl A a) H
    env.add_theorem(congr2_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {a, A}, {b, A}, {H, Eq(a, b)}}, Eq(f(a), f(b))),
                    Fun({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {a, A}, {b, A}, {H, Eq(a, b)}},
                        Subst(A, Fun({x, A}, Eq(f(a), f(x))), a, b, Refl(A, a), H)));

    // Congr : Pi (A : Type u) (B : A -> Type u) (f g : Pi (x : A) B x) (a b : A) (H1 : f = g) (H2 : a = b), f a = g b :=
    //         xTrans (B a) (B b) (f a) (f b) (g b) (congr2 A B f g b H1) (congr1 A B f a b H2)
    env.add_theorem(congr_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {a, A}, {b, A}, {H1, Eq(f, g)}, {H2, Eq(a, b)}}, Eq(f(a), g(b))),
                    Fun({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {a, A}, {b, A}, {H1, Eq(f, g)}, {H2, Eq(a, b)}},
                        xTrans(B(a), B(b), f(a), f(b), g(b),
                               Congr2(A, B, f, a, b, H2), Congr1(A, B, f, g, b, H1))));

    // EqMP : Pi (a b: Bool) (H1 : a = b) (H2 : a), b :=
    //          Subst Bool (Fun x : Bool => x) a b H2 H1
    env.add_theorem(eq_mp_fn_name, Pi({{a, Bool}, {b, Bool}, {H1, Eq(a, b)}, {H2, a}}, b),
                    Fun({{a, Bool}, {b, Bool}, {H1, Eq(a, b)}, {H2, a}},
                        Subst(Bool, Fun({x, Bool}, x), a, b, H2, H1)));

    // EqTElim : Pi (a : Bool) (H : a = True), a := EqMP(True, a, Symm(Bool, a, True, H), Truth)
    env.add_theorem(eqt_elim_fn_name, Pi({{a, Bool}, {H, Eq(a, True)}}, a),
                    Fun({{a, Bool}, {H, Eq(a, True)}},
                        EqMP(True, a, Symm(Bool, a, True, H), Truth)));

    // EqTIntro : Pi (a : Bool) (H : a), a = True
    // env.add_theorem(eqt_intro_fn_name, Pi({{a, Bool}, {H, a}}, Eq(a, True)),
    //                Fun({{a, Bool}, {H, a}}

    // ForallElim : Pi (A : Type u) (P : A -> bool) (H : (forall A P)) (a : A), P a
    env.add_theorem(forall_elim_fn_name, Pi({{A, TypeU}, {P, A_pred}, {H, mk_forall(A, P)}, {a, A}}, P(a)),
                    Fun({{A, TypeU}, {P, A_pred}, {H, mk_forall(A, P)}, {a, A}},
                        EqTElim(P(a), Congr1(A, Fun({x, A}, Bool), P, Fun({x, A}, True), a, H))));

#if 0
    // STOPPED HERE

    // foralli : Pi (A : Type u) (P : A -> bool) (H : Pi (x : A), P x), (forall A P)
    env.add_axiom(foralli_fn_name, Pi({{A, TypeU}, {P, A_pred}, {H, Pi({x, A}, P(x))}}, Forall(A, P)));

    // ext : Pi (A : Type u) (B : A -> Type u) (f g : Pi (x : A) B x) (H : Pi x : A, (f x) = (g x)), f = g
    env.add_axiom(ext_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {H, Pi({x, A}, Eq(f(x), g(x)))}}, Eq(f, g)));


    // domain_inj : Pi (A A1: Type u) (B : A -> Type u) (B1 : A1 -> Type u) (H : (Pi (x : A), B x) = (Pi (x : A1), B1 x)), A = A1
    expr piA1B1x = Pi({x, A1}, B1(x));
    expr A1_arrow_u = A1 >> TypeU;
    env.add_axiom(domain_inj_fn_name, Pi({{A, TypeU}, {A1, TypeU}, {B, A_arrow_u}, {B1, A1_arrow_u}, {H, Eq(piABx, piA1B1x)}}, Eq(A, A1)));
    // range_inj : Pi (A A1: Type u) (B : A -> Type u) (B1 : A1 -> Type u) (a : A) (a1 : A1) (H : (Pi (x : A), B x) = (Pi (x : A1), B1 x)), (B a) = (B1 a1)
    env.add_axiom(range_inj_fn_name, Pi({{A, TypeU}, {A1, TypeU}, {B, A_arrow_u}, {B1, A1_arrow_u}, {a, A}, {a1, A1}, {H, Eq(piABx, piA1B1x)}}, Eq(B(a), B1(a1))));
#endif
}
}
