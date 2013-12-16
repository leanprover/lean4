/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/builtin.h"

namespace lean {
expr mk_trivial();
/** \brief (Theorem) Trivial : True */
#define Trivial mk_trivial()

expr mk_true_ne_false();
/** \brief (Theorem) TrueNeFalse : Not(True = False) */
#define TrueNeFalse mk_true_ne_false();

expr mk_em_fn();
/** \brief (Theorem) a : Bool |- EM(a) : Or(a, Not(a)) */
inline expr EM(expr const & a) { return mk_app(mk_em_fn(), a); }

expr mk_false_elim_fn();
/** \brief (Theorem) a : Bool, H : False |- FalseElim(a, H) : a */
inline expr FalseElim(expr const & a, expr const & H) { return mk_app(mk_false_elim_fn(), a, H); }

expr mk_absurd_fn();
/** \brief (Theorem) {a : Bool}, H1 : a, H2 : Not(a) |- Absurd(a, H1, H2) : False */
inline expr Absurd(expr const & a, expr const & H1, expr const & H2) { return mk_app(mk_absurd_fn(), a, H1, H2); }

expr mk_double_neg_fn();
/** \brief (Theorem) a : Bool |- DoubleNeg(a) : Neg(Neg(a)) = a */
inline expr DoubleNeg(expr const & a) { return mk_app(mk_double_neg_fn(), a); }

expr mk_double_neg_elim_fn();
/** \brief (Theorem) {P : Bool}, H : Not (Not P) |- DoubleNegElim(P, H) : P */
inline expr DoubleNegElim(expr const & P, expr const & H) { return mk_app(mk_double_neg_elim_fn(), P, H); }

expr mk_mt_fn();
/** \brief (Theorem) {a b : Bool}, H1 : a => b, H2 : Not(b) |- MT(a, b, H1, H2) : Not(a) */
inline expr MT(expr const & a, expr const & b, expr const & H1, expr const & H2) { return mk_app(mk_mt_fn(), a, b, H1, H2); }

expr mk_contrapos_fn();
/** \brief (Theorem) {a b : Bool}, H : a => b |- Contrapos(a, b, H): Neg(b) => Neg(a) */
inline expr Contrapos(expr const & a, expr const & b, expr const & H) { return mk_app(mk_contrapos_fn(), a, b, H); }

expr mk_false_imp_any_fn();
/** \brief (Theorem) a : Bool |- false => a */
inline expr FalseImpAny(expr const & a) { return mk_app(mk_false_imp_any_fn(), a); }

expr mk_absurd_imp_any_fn();
/** \brief (Theorem) {a c : Bool}, H1 : a, H2 : Not(a) |- AbsurdImpAny(a, H1, H2) : c */
inline expr AbsurdImpAny(expr const & a, expr const & c, expr const & H1, expr const & H2) {
    return mk_app(mk_absurd_imp_any_fn(), a, c, H1, H2);
}

expr mk_eq_mp_fn();
/** \brief (Theorem) {a b : Bool}, H1 : a = b, H2 : a |- EqMP(a, b, H1, H2) : b */
inline expr EqMP(expr const & a, expr const & b, expr const & H1, expr const & H2) { return mk_app(mk_eq_mp_fn(), a, b, H1, H2); }

expr mk_not_imp1_fn();
/** \brief (Theorem) {a b : Bool}, H : Not(Implies(a, b)) |- NotImp1(a, b, H) : a */
inline expr NotImp1(expr const & a, expr const & b, expr const & H) { return mk_app(mk_not_imp1_fn(), a, b, H); }

expr mk_not_imp2_fn();
/** \brief (Theorem) {a b : Bool}, H : Not(Implies(a, b)) |- NotImp2(a, b, H) : Not(b) */
inline expr NotImp2(expr const & a, expr const & b, expr const & H) { return mk_app(mk_not_imp2_fn(), a, b, H); }

expr mk_conj_fn();
/** \brief (Theorem) {a b : Bool}, H1 : a, H2 : b |- Conj(a, b, H1, H2) : And(a, b) */
inline expr Conj(expr const & a, expr const & b, expr const & H1, expr const & H2) { return mk_app(mk_conj_fn(), a, b, H1, H2); }

expr mk_conjunct1_fn();
/** \brief (Theorem) {a b : Bool}, H : And(a, b) |- Conjunct1(a, b, H) : a */
inline expr Conjunct1(expr const & a, expr const & b, expr const & H) { return mk_app(mk_conjunct1_fn(), a, b, H); }

expr mk_conjunct2_fn();
/** \brief (Theorem) {a b : Bool}, H : And(a, b) |- Conjunct2(a, b, H) : b */
inline expr Conjunct2(expr const & a, expr const & b, expr const & H) { return mk_app(mk_conjunct2_fn(), a, b, H); }

expr mk_disj1_fn();
/** \brief (Theorem) a b : Bool, H : a |- Disj1(a, b, H) : Or(a, b) */
inline expr Disj1(expr const & a, expr const & b, expr const & H) { return mk_app(mk_disj1_fn(), a, b, H); }

expr mk_disj2_fn();
/** \brief (Theorem) {b} a : Bool, H : b |- Disj2(a, b, H) : Or(a, b) */
inline expr Disj2(expr const & b, expr const & a, expr const & H) { return mk_app(mk_disj2_fn(), b, a, H); }

expr mk_disj_cases_fn();
/** \brief (Theorem) {a b c : Bool}, H1 : Or(a, b), H2 : a -> c, H3 : b -> c |- DisjCases(a, b, c, H1, H2, H3) : c */
inline expr DisjCases(expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2, expr const & H3) { return mk_app({mk_disj_cases_fn(), a, b, c, H1, H2, H3}); }

expr mk_refute_fn();
/** \brief (Theorem) {a : Bool} (H : not a -> false) |- Refute(a, H) : a */
inline expr Refute(expr const & a, expr const & H) { return mk_app({mk_refute_fn(), a, H}); }

expr mk_symm_fn();
/** \brief (Theorem) {A : Type u}, {a b : A}, H : a = b |- Symm(A, a, b, H) : b = a */
inline expr Symm(expr const & A, expr const & a, expr const & b, expr const & H) { return mk_app(mk_symm_fn(), A, a, b, H); }

expr mk_trans_fn();
/** \brief (Theorem) {A : Type u}, {a b c : A}, H1 : a = b, H2 : b = c |- Trans(A, a, b, c, H1, H2) : a = c */
inline expr Trans(expr const & A, expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2) { return mk_app({mk_trans_fn(), A, a, b, c, H1, H2}); }

expr mk_eqt_elim_fn();
/** \brief (Theorem) {a : Bool}, H : a = True |- EqTElim(a, H) : a */
inline expr EqTElim(expr const & a, expr const & H) { return mk_app(mk_eqt_elim_fn(), a, H); }

expr mk_eqt_intro_fn();
/** \brief (Theorem) {a : Bool}, H : a |- EqTIntro(a, H) : a = True */
inline expr EqTIntro(expr const & a, expr const & H) { return mk_app(mk_eqt_intro_fn(), a, H); }

expr mk_congr1_fn();
/** \brief (Theorem) {A : Type u}, {B : A -> Type u}, {f g : (Pi x : A, B x)}, a : A, H : f = g |- Congr2(A, B, f, g, a, H) : f a = g a */
inline expr Congr1(expr const & A, expr const & B, expr const & f, expr const & g, expr const & a, expr const & H) { return mk_app({mk_congr1_fn(), A, B, f, g, a, H}); }

expr mk_congr2_fn();
/** \brief (Theorem) {A : Type u}, {B : A -> Type u}, {a b : A}, f : (Pi x : A, B x), H : a = b |- Congr1(A, B, f, a, b, H) : f a = f b */
inline expr Congr2(expr const & A, expr const & B, expr const & a, expr const & b, expr const & f, expr const & H) { return mk_app({mk_congr2_fn(), A, B, a, b, f, H}); }

expr mk_congr_fn();
/** \brief (Theorem) {A : Type u}, {B : A -> Type u}, {f g : (Pi x : A, B x)}, {a b : A}, H1 : f = g, H2 : a = b |- Congr(A, B, f, g, a, b, H1, H2) : f a = g b */
inline expr Congr(expr const & A, expr const & B, expr const & f, expr const & g, expr const & a, expr const & b, expr const & H1, expr const & H2) { return mk_app({mk_congr_fn(), A, B, f, g, a, b, H1, H2}); }

expr mk_forall_elim_fn();
// \brief (Theorem) {A : Type u}, {P : A -> Bool}, H : (Forall A P), a : A |- ForallElim(A, P, H, a) : P a
inline expr ForallElim(expr const & A, expr const & P, expr const & H, expr const & a) { return mk_app(mk_forall_elim_fn(), A, P, H, a); }

expr mk_forall_intro_fn();
// \brief (Theorem) {A : Type u} {P : A -> bool} (H : Pi (x : A), P x) |- ForallIntro(A, P, H) : forall x : A, P
inline expr ForallIntro(expr const & A, expr const & P, expr const & H) { return mk_app(mk_forall_intro_fn(), A, P, H); }

expr mk_exists_elim_fn();
// \brief (Theorem) {A : Type U} {P : A -> Bool} {B : Bool} (H1 : exists x : A, P x) (H2 : Pi (a : A) (H : P a) |- ExistsElim(A, P, B, H1, H2) : B
inline expr ExistsElim(expr const & A, expr const & P, expr const & B, expr const & H1, expr const & H2) { return mk_app({mk_exists_elim_fn(), A, P, B, H1, H2}); }

expr mk_exists_intro_fn();
// \brief (Theorem) {A : Type u}, {P : A -> Bool}, a : A,  H : P a |- ExistsIntro(A, P, a, H) : exists x : A, P
inline expr ExistsIntro(expr const & A, expr const & P, expr const & a, expr const & H) { return mk_app(mk_exists_intro_fn(), A, P, a, H); }

/** \brief Add basic theorems to Environment */
void import_basic_thms(environment const & env);
}
