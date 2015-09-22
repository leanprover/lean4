/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Properties of is_trunc and trunctype
-/

-- NOTE: the fact that (is_trunc n A) is a mere proposition is proved in .hprop_trunc

import types.pi types.eq types.equiv ..function

open eq sigma sigma.ops pi function equiv is_trunc.trunctype
     is_equiv prod is_trunc.trunc_index pointed nat

namespace is_trunc
  variables {A B : Type} {n : trunc_index}

  /- theorems about trunctype -/
  protected definition trunctype.sigma_char.{l} (n : trunc_index) :
    (trunctype.{l} n) ≃ (Σ (A : Type.{l}), is_trunc n A) :=
  begin
    fapply equiv.MK,
    { intro A, exact (⟨carrier A, struct A⟩)},
    { intro S, exact (trunctype.mk S.1 S.2)},
    { intro S, induction S with S1 S2, reflexivity},
    { intro A, induction A with A1 A2, reflexivity},
  end

  definition trunctype_eq_equiv (n : trunc_index) (A B : n-Type) :
    (A = B) ≃ (carrier A = carrier B) :=
  calc
    (A = B) ≃ (to_fun (trunctype.sigma_char n) A = to_fun (trunctype.sigma_char n) B)
              : eq_equiv_fn_eq_of_equiv
      ... ≃ ((to_fun (trunctype.sigma_char n) A).1 = (to_fun (trunctype.sigma_char n) B).1)
             : equiv.symm (!equiv_subtype)
      ... ≃ (carrier A = carrier B) : equiv.refl

  theorem is_trunc_is_embedding_closed (f : A → B) [Hf : is_embedding f] [HB : is_trunc n B]
    (Hn : -1 ≤ n) : is_trunc n A :=
  begin
    induction n with n,
      {exact !empty.elim Hn},
      {apply is_trunc_succ_intro, intro a a',
         fapply @is_trunc_is_equiv_closed_rev _ _ n (ap f)}
  end

  theorem is_trunc_is_retraction_closed (f : A → B) [Hf : is_retraction f]
    (n : trunc_index) [HA : is_trunc n A] : is_trunc n B :=
  begin
    revert A B f Hf HA,
    induction n with n IH,
    { intro A B f Hf HA, induction Hf with g ε, fapply is_contr.mk,
      { exact f (center A)},
      { intro b, apply concat,
        { apply (ap f), exact (center_eq (g b))},
        { apply ε}}},
    { intro A B f Hf HA, induction Hf with g ε,
      apply is_trunc_succ_intro, intro b b',
      fapply (IH (g b = g b')),
      { intro q, exact ((ε b)⁻¹ ⬝ ap f q ⬝ ε b')},
      { apply (is_retraction.mk (ap g)),
        { intro p, induction p, {rewrite [↑ap, con.left_inv]}}},
      { apply is_trunc_eq}}
  end

  definition is_embedding_to_fun (A B : Type) : is_embedding (@to_fun A B)  :=
  λf f', !is_equiv_ap_to_fun

  theorem is_trunc_trunctype [instance] (n : trunc_index) : is_trunc n.+1 (n-Type) :=
  begin
    apply is_trunc_succ_intro, intro X Y,
    fapply is_trunc_equiv_closed,
      {apply equiv.symm, apply trunctype_eq_equiv},
    fapply is_trunc_equiv_closed,
      {apply equiv.symm, apply eq_equiv_equiv},
    induction n,
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
  theorem is_hset_of_axiom_K {A : Type} (K : Π{a : A} (p : a = a), p = idp) : is_hset A :=
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
    (λp, p ▸ refl a)

  local attribute not [reducible]
  theorem is_hset_of_double_neg_elim {A : Type} (H : Π(a b : A), ¬¬a = b → a = b)
    : is_hset A :=
  is_hset_of_relation (λa b, ¬¬a = b) _ (λa n, n idp) H

  section
  open decidable
  --this is proven differently in init.hedberg
  theorem is_hset_of_decidable_eq (A : Type) [H : decidable_eq A] : is_hset A :=
  is_hset_of_double_neg_elim (λa b, by_contradiction)
  end

  theorem is_trunc_of_axiom_K_of_leq {A : Type} (n : trunc_index) (H : -1 ≤ n)
    (K : Π(a : A), is_trunc n (a = a)) : is_trunc (n.+1) A :=
  @is_trunc_succ_intro _ _ (λa b, is_trunc_of_imp_is_trunc_of_leq H (λp, eq.rec_on p !K))

  theorem is_trunc_succ_of_is_trunc_loop (Hn : -1 ≤ n) (Hp : Π(a : A), is_trunc n (a = a))
    : is_trunc (n.+1) A :=
  begin
    apply is_trunc_succ_intro, intros a a',
    apply is_trunc_of_imp_is_trunc_of_leq Hn, intro p,
    induction p, apply Hp
  end

  theorem is_trunc_succ_iff_is_trunc_loop (A : Type) (Hn : -1 ≤ n) :
    is_trunc (n.+1) A ↔ Π(a : A), is_trunc n (a = a) :=
  iff.intro _ (is_trunc_succ_of_is_trunc_loop Hn)

  theorem is_trunc_iff_is_contr_loop_succ (n : ℕ) (A : Type)
    : is_trunc n A ↔ Π(a : A), is_contr (Ω[succ n](Pointed.mk a)) :=
  begin
    revert A, induction n with n IH,
      { intros, esimp [Iterated_loop_space], apply iff.intro,
        { intros H a, apply is_contr.mk idp, apply is_hprop.elim},
        { intro H, apply is_hset_of_axiom_K, intros, apply is_hprop.elim}},
      { intros, transitivity _, apply @is_trunc_succ_iff_is_trunc_loop n, constructor,
        apply iff.pi_iff_pi, intros,
        transitivity _, apply IH,
        assert H : Πp : a = a, Ω(Pointed.mk p) = Ω(Pointed.mk (idpath a)),
        { intros, fapply Pointed_eq,
          { esimp, transitivity _,
            apply eq_equiv_fn_eq_of_equiv (equiv_eq_closed_right _ p⁻¹),
            esimp, apply eq_equiv_eq_closed, apply con.right_inv, apply con.right_inv},
          { esimp, apply con.left_inv}},
        transitivity _,
          apply iff.pi_iff_pi, intro p,
          rewrite [↑Iterated_loop_space,H],
          apply iff.refl,
        apply iff.imp_iff, reflexivity}
  end

  theorem is_trunc_iff_is_contr_loop (n : ℕ) (A : Type)
    : is_trunc (n.-2.+1) A ↔ (Π(a : A), is_contr (Ω[n](pointed.Mk a))) :=
  begin
    induction n with n,
    { esimp [sub_two,Iterated_loop_space], apply iff.intro,
        intro H a, exact is_contr_of_inhabited_hprop a,
        intro H, apply is_hprop_of_imp_is_contr, exact H},
    { apply is_trunc_iff_is_contr_loop_succ},
  end

end is_trunc open is_trunc

namespace trunc
  variable {A : Type}

  protected definition code (n : trunc_index) (aa aa' : trunc n.+1 A) : n-Type :=
  trunc.rec_on aa (λa, trunc.rec_on aa' (λa', trunctype.mk' n (trunc n (a = a'))))

  protected definition encode (n : trunc_index) (aa aa' : trunc n.+1 A) : aa = aa' → trunc.code n aa aa' :=
  begin
    intro p, induction p, apply (trunc.rec_on aa),
    intro a, esimp [trunc.code,trunc.rec_on], exact (tr idp)
  end

  protected definition decode (n : trunc_index) (aa aa' : trunc n.+1 A) : trunc.code n aa aa' → aa = aa' :=
  begin
    eapply (trunc.rec_on aa'), eapply (trunc.rec_on aa),
    intro a a' x, esimp [trunc.code, trunc.rec_on] at x,
    apply (trunc.rec_on x), intro p, exact (ap tr p)
  end

  definition trunc_eq_equiv [constructor] (n : trunc_index) (aa aa' : trunc n.+1 A)
    : aa = aa' ≃ trunc.code n aa aa' :=
  begin
    fapply equiv.MK,
    { apply trunc.encode},
    { apply trunc.decode},
    { eapply (trunc.rec_on aa'), eapply (trunc.rec_on aa),
      intro a a' x, esimp [trunc.code, trunc.rec_on] at x,
      refine (@trunc.rec_on n _ _ x _ _),
        intro x, apply is_trunc_eq,
        intro p, induction p, reflexivity},
    { intro p, induction p, apply (trunc.rec_on aa), intro a, exact idp},
  end

  definition tr_eq_tr_equiv [constructor] (n : trunc_index) (a a' : A)
    : (tr a = tr a' :> trunc n.+1 A) ≃ trunc n (a = a') :=
  !trunc_eq_equiv

  definition is_trunc_trunc_of_is_trunc [instance] [priority 500] (A : Type)
    (n m : trunc_index) [H : is_trunc n A] : is_trunc n (trunc m A) :=
  begin
    revert A m H, eapply (trunc_index.rec_on n),
    { clear n, intro A m H, apply is_contr_equiv_closed,
      { apply equiv.symm, apply trunc_equiv, apply (@is_trunc_of_leq _ -2), exact unit.star} },
    { clear n, intro n IH A m H, induction m with m,
      { apply (@is_trunc_of_leq _ -2), exact unit.star},
      { apply is_trunc_succ_intro, intro aa aa',
        apply (@trunc.rec_on _ _ _ aa  (λy, !is_trunc_succ_of_is_hprop)),
        eapply (@trunc.rec_on _ _ _ aa' (λy, !is_trunc_succ_of_is_hprop)),
        intro a a', apply (is_trunc_equiv_closed_rev),
        { apply tr_eq_tr_equiv},
        { exact (IH _ _ _)}}}
  end

  open equiv.ops
  definition unique_choice {P : A → Type} [H : Πa, is_hprop (P a)] (f : Πa, ∥ P a ∥) (a : A)
    : P a :=
  !trunc_equiv (f a)


end trunc open trunc

namespace function
  variables {A B : Type}
  definition is_surjective_of_is_equiv [instance] (f : A → B) [H : is_equiv f] : is_surjective f :=
  λb, !center

  definition is_equiv_equiv_is_embedding_times_is_surjective [constructor] (f : A → B)
    : is_equiv f ≃ (is_embedding f × is_surjective f) :=
  equiv_of_is_hprop (λH, (_, _))
                    (λP, prod.rec_on P (λH₁ H₂, !is_equiv_of_is_surjective_of_is_embedding))

end function
