/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.trunc
Authors: Floris van Doorn

Properties of is_trunc and trunctype
-/

--NOTE: the fact that (is_trunc n A) is a mere proposition is proved in .hprop_trunc

import types.pi types.eq types.equiv .function

open eq sigma sigma.ops pi function equiv is_trunc.trunctype is_equiv prod

namespace is_trunc
  variables {A B : Type} {n : trunc_index}

  definition is_trunc_succ_of_imp_is_trunc_succ (H : A → is_trunc (n.+1) A) : is_trunc (n.+1) A :=
  @is_trunc_succ_intro _ _ (λx y, @is_trunc_eq _ _ (H x) x y)

  definition is_trunc_of_imp_is_trunc_of_leq (Hn : -1 ≤ n) (H : A → is_trunc n A) : is_trunc n A :=
  trunc_index.rec_on n (λHn H, empty.rec _ Hn)
                       (λn IH Hn, is_trunc_succ_of_imp_is_trunc_succ)
                       Hn H

  /- theorems about trunctype -/
  protected definition trunctype.sigma_char.{l} (n : trunc_index) :
    (trunctype.{l} n) ≃ (Σ (A : Type.{l}), is_trunc n A) :=
  begin
    fapply equiv.MK,
    { intro A, exact (⟨carrier A, struct A⟩)},
    { intro S, exact (trunctype.mk S.1 S.2)},
    { intro S, apply (sigma.rec_on S), intros [S1, S2], apply idp},
    { intro A, apply (trunctype.rec_on A), intros [A1, A2], apply idp},
  end

  definition trunctype_eq_equiv (n : trunc_index) (A B : n-Type) :
    (A = B) ≃ (carrier A = carrier B) :=
  calc
    (A = B) ≃ (to_fun (trunctype.sigma_char n) A = to_fun (trunctype.sigma_char n) B)
              : eq_equiv_fn_eq_of_equiv
      ... ≃ ((to_fun (trunctype.sigma_char n) A).1 = (to_fun (trunctype.sigma_char n) B).1)
             : equiv.symm (!equiv_subtype)
      ... ≃ (carrier A = carrier B) : equiv.refl

  definition is_trunc_is_embedding_closed (f : A → B) [Hf : is_embedding f] [HB : is_trunc n B]
    (Hn : -1 ≤ n) : is_trunc n A :=
  begin
    cases n with [n],
      {exact (!empty.elim Hn)},
      {apply is_trunc_succ_intro, intros [a, a'],
         fapply (@is_trunc_is_equiv_closed_rev _ _ n (ap f))}
  end

  definition is_trunc_is_retraction_closed (f : A → B) [Hf : is_retraction f]
    (n : trunc_index) [HA : is_trunc n A] : is_trunc n B :=
  begin
    reverts [A, B, f, Hf, HA],
    apply (trunc_index.rec_on n),
    { clear n, intros [A, B, f, Hf, HA], cases Hf with [g, ε], fapply is_contr.mk,
      { exact (f (center A))},
      { intro b, apply concat,
        { apply (ap f), exact (center_eq (g b))},
        { apply ε}}},
    { clear n, intros [n, IH, A, B, f, Hf, HA], cases Hf with [g, ε],
      apply is_trunc_succ_intro, intros [b, b'],
      fapply (IH (g b = g b')),
      { intro q, exact ((ε b)⁻¹ ⬝ ap f q ⬝ ε b')},
      { apply (is_retraction.mk (ap g)),
        { intro p, cases p, {rewrite [↑ap, con_idp, con.left_inv]}}},
      { apply is_trunc_eq}}
  end

  definition is_embedding_to_fun (A B : Type) : is_embedding (@to_fun A B)  :=
  is_embedding.mk (λf f', !is_equiv_ap_to_fun)

  definition is_trunc_trunctype [instance] (n : trunc_index) : is_trunc n.+1 (n-Type) :=
  begin
    apply is_trunc_succ_intro, intros [X, Y],
    fapply is_trunc_equiv_closed,
      {apply equiv.symm, apply trunctype_eq_equiv},
    fapply is_trunc_equiv_closed,
      {apply equiv.symm, apply eq_equiv_equiv},
    cases n,
      {apply @is_contr_of_inhabited_hprop,
        {apply is_trunc_is_embedding_closed,
          {apply is_embedding_to_fun} ,
          {exact unit.star}},
        {apply equiv_of_is_contr_of_is_contr}},
      {apply is_trunc_is_embedding_closed,
        {apply is_embedding_to_fun},
        {exact unit.star}}
  end


  /- theorems about decidable equality and axiom K -/
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

end is_trunc open is_trunc

namespace trunc
  variable {A : Type}

  definition trunc_eq_type (n : trunc_index) (aa aa' : trunc n.+1 A) : n-Type :=
  trunc.rec_on aa (λa, trunc.rec_on aa' (λa', trunctype.mk' n (trunc n (a = a'))))

  definition trunc_eq_equiv (n : trunc_index) (aa aa' : trunc n.+1 A)
    : aa = aa' ≃ trunc_eq_type n aa aa' :=
  begin
    fapply equiv.MK,
    { intro p, cases p, apply (trunc.rec_on aa),
      intro a, esimp [trunc_eq_type,trunc.rec_on], exact (tr idp)},
    { apply (trunc.rec_on aa'), apply (trunc.rec_on aa),
      intros [a, a', x], esimp [trunc_eq_type, trunc.rec_on] at x,
      apply (trunc.rec_on x), intro p, exact (ap tr p)},
    {
      -- apply (trunc.rec_on aa'), apply (trunc.rec_on aa),
      -- intros [a, a', x], esimp [trunc_eq_type, trunc.rec_on] at x,
      -- apply (trunc.rec_on x), intro p,
      -- cases p, esimp [trunc.rec_on,eq.cases_on,compose,id], -- apply idp --?
      apply sorry},
    { intro p, cases p, apply (trunc.rec_on aa), intro a, apply sorry},
  end

  definition tr_eq_tr_equiv (n : trunc_index) (a a' : A)
    : (tr a = tr a' :> trunc n.+1 A) ≃ trunc n (a = a') :=
  !trunc_eq_equiv

  definition is_trunc_trunc_of_is_trunc [instance] [priority 500] (A : Type)
    (n m : trunc_index) [H : is_trunc n A] : is_trunc n (trunc m A) :=
  begin
    reverts [A, m, H], apply (trunc_index.rec_on n),
    { clear n, intros [A, m, H], apply is_contr_equiv_closed,
      { apply equiv_trunc, apply (@is_trunc_of_leq _ -2), exact unit.star} },
    { clear n, intros [n, IH, A, m, H], cases m with [m],
      { apply (@is_trunc_of_leq _ -2), exact unit.star},
      { apply is_trunc_succ_intro, intros [aa, aa'],
        apply (@trunc.rec_on _ _ _ aa  (λy, !is_trunc_succ_of_is_hprop)),
        apply (@trunc.rec_on _ _ _ aa' (λy, !is_trunc_succ_of_is_hprop)),
        intros [a, a'], apply (is_trunc_equiv_closed_rev),
        { apply tr_eq_tr_equiv},
        { exact (IH _ _ _)}}}
  end

end trunc open trunc

namespace function
  variables {A B : Type}
  definition is_surjective_of_is_equiv [instance] (f : A → B) [H : is_equiv f] : is_surjective f :=
  is_surjective.mk (λb, !center)

  definition is_equiv_equiv_is_embedding_times_is_surjective (f : A → B)
    : is_equiv f ≃ (is_embedding f × is_surjective f) :=
  equiv_of_is_hprop (λH, (_, _))
                    (λP, prod.rec_on P (λH₁ H₂, !is_equiv_of_is_surjective_of_is_embedding))

end function
