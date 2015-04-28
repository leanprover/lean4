/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.trunc
Authors: Jakob von Raumer, Floris van Doorn

Properties of is_trunc
-/

import types.pi types.eq

open sigma sigma.ops pi function eq equiv eq funext
namespace is_trunc

  definition is_contr.sigma_char (A : Type) :
    (Σ (center : A), Π (a : A), center = a) ≃ (is_contr A) :=
  begin
    fapply equiv.mk,
     {intro S, apply is_contr.mk, exact S.2},
     {fapply is_equiv.adjointify,
       {intro H, apply sigma.mk, exact (@center_eq A H)},
       {intro H, apply (is_trunc.rec_on H), intro Hint,
        apply (contr_internal.rec_on Hint), intros [H1, H2],
        apply idp},
       {intro S, cases S, apply idp}}
  end

  definition is_trunc.pi_char (n : trunc_index) (A : Type) :
    (Π (x y : A), is_trunc n (x = y)) ≃ (is_trunc (n .+1) A) :=
  begin
    fapply equiv.MK,
      {intro H, apply is_trunc_succ_intro},
      {intros [H, x, y], apply is_trunc_eq},
      {intro H, apply (is_trunc.rec_on H), intro Hint, apply idp},
      {intro P, apply eq_of_homotopy, intro a, apply eq_of_homotopy, intro b,
    esimp [function.id,compose,is_trunc_succ_intro,is_trunc_eq],
    generalize (P a b), intro H, apply (is_trunc.rec_on H), intro H', apply idp},
  end

  definition is_hprop_is_trunc [instance] (n : trunc_index) :
    Π (A : Type), is_hprop (is_trunc n A) :=
  begin
    apply (trunc_index.rec_on n),
      {intro A,
       apply is_trunc_is_equiv_closed, apply equiv.to_is_equiv,
       apply is_contr.sigma_char,
       apply (@is_hprop.mk), intros,
       fapply sigma_eq, apply x.2,
       apply (@is_hprop.elim),
       apply is_trunc_pi, intro a,
       apply is_hprop.mk, intros [w, z],
       have H : is_hset A,
       begin
         apply is_trunc_succ, apply is_trunc_succ,
         apply is_contr.mk, exact y.2
       end,
       fapply (@is_hset.elim A _ _ _ w z)},
     {intros [n', IH, A],
      apply is_trunc_is_equiv_closed,
        apply equiv.to_is_equiv,
        apply is_trunc.pi_char},
  end

  definition is_trunc_succ_of_imp_is_trunc_succ {A : Type} {n : trunc_index} (H : A → is_trunc (n.+1) A)
      : is_trunc (n.+1) A :=
  @is_trunc_succ_intro _ _ (λx y, @is_trunc_eq _ _ (H x) x y)

  definition is_trunc_of_imp_is_trunc_of_leq {A : Type} {n : trunc_index} (Hn : -1 ≤ n)
      (H : A → is_trunc n A) : is_trunc n A :=
  trunc_index.rec_on n (λHn H, empty.rec _ Hn)
                       (λn IH Hn, is_trunc_succ_of_imp_is_trunc_succ)
                       Hn H

  definition is_hset_of_axiom_K {A : Type} (K : Π{a : A} (p : a = a), p = idp) : is_hset A :=
  is_hset.mk _ (λa b p q, eq.rec_on q K p)

  theorem is_hset_of_relation.{u} {A : Type.{u}} (R : A → A → Type.{u})
    (mere : Π(a b : A), is_hprop (R a b)) (refl : Π(a : A), R a a)
    (imp : Π{a b : A}, R a b → a = b) : is_hset A :=
  is_hset_of_axiom_K
    (λa p,
      have H2 : transport (λx, R a x → a = x) p (@imp a a) = @imp a a, from !apd,
      have H3 : Π(r : R a a), transport (λx, a = x) p (imp r)
                              = imp (transport (λx, R a x) p r), from
        to_fun (equiv.symm !heq_pi) H2,
      have H4 : imp (refl a) ⬝ p = imp (refl a), from
        calc
          imp (refl a) ⬝ p = transport (λx, a = x) p (imp (refl a)) : transport_eq_r
            ... = imp (transport (λx, R a x) p (refl a)) : H3
            ... = imp (refl a) : is_hprop.elim,
      cancel_left H4)

  definition relation_equiv_eq {A : Type} (R : A → A → Type)
    (mere : Π(a b : A), is_hprop (R a b)) (refl : Π(a : A), R a a)
    (imp : Π{a b : A}, R a b → a = b) (a b : A) : R a b ≃ a = b :=
  @equiv_of_is_hprop _ _ _
    (@is_trunc_eq _ _ (is_hset_of_relation R mere refl @imp) a b)
    imp
    (λp, p ▹ refl a)

  local attribute not [reducible]
  definition is_hset_of_double_neg_elim {A : Type} (H : Π(a b : A), ¬¬a = b → a = b)
    : is_hset A :=
  is_hset_of_relation (λa b, ¬¬a = b) _ (λa n, n idp) H

  section
  open decidable
  --this is proven differently in init.hedberg
  definition is_hset_of_decidable_eq (A : Type)
    [H : decidable_eq A] : is_hset A :=
  is_hset_of_double_neg_elim (λa b, by_contradiction)
  end

  definition is_trunc_of_axiom_K_of_leq {A : Type} (n : trunc_index) (H : -1 ≤ n)
    (K : Π(a : A), is_trunc n (a = a)) : is_trunc (n.+1) A :=
  @is_trunc_succ_intro _ _ (λa b, is_trunc_of_imp_is_trunc_of_leq H (λp, eq.rec_on p !K))

  open trunctype equiv equiv.ops

  protected definition trunctype.sigma_char.{l} (n : trunc_index) :
    (trunctype.{l} n) ≃ (Σ (A : Type.{l}), is_trunc n A) :=
  begin
    fapply equiv.MK,
    /--/  intro A, exact (⟨carrier A, struct A⟩),
    /--/  intro S, exact (trunctype.mk S.1 S.2),
    /--/  intro S, apply (sigma.rec_on S), intros [S1, S2], apply idp,
    intro A, apply (trunctype.rec_on A), intros [A1, A2], apply idp,
  end

  protected definition trunctype_eq_equiv (n : trunc_index) (A B : n-Type) :
    (A = B) ≃ (carrier A = carrier B) :=
  calc
    (A = B) ≃ (trunctype.sigma_char n A = trunctype.sigma_char n B) : eq_equiv_fn_eq_of_equiv
      ... ≃ ((trunctype.sigma_char n A).1 = (trunctype.sigma_char n B).1) : equiv.symm (!equiv_subtype)
      ... ≃ (carrier A = carrier B) : equiv.refl


end is_trunc
