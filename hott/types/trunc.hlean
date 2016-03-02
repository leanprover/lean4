/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Properties of is_trunc and trunctype
-/

-- NOTE: the fact that (is_trunc n A) is a mere proposition is proved in .prop_trunc

import .pointed2 ..function algebra.order types.nat.order

open eq sigma sigma.ops pi function equiv trunctype
     is_equiv prod is_trunc.trunc_index pointed nat is_trunc algebra

namespace is_trunc

  namespace trunc_index

    definition minus_one_le_succ (n : trunc_index) : -1 ≤ n.+1 :=
    succ_le_succ (minus_two_le n)

    definition zero_le_of_nat (n : ℕ) : 0 ≤ of_nat n :=
    succ_le_succ !minus_one_le_succ

    open decidable
    protected definition has_decidable_eq [instance] : Π(n m : ℕ₋₂), decidable (n = m)
    | has_decidable_eq -2     -2     := inl rfl
    | has_decidable_eq (n.+1) -2     := inr (by contradiction)
    | has_decidable_eq -2     (m.+1) := inr (by contradiction)
    | has_decidable_eq (n.+1) (m.+1) :=
        match has_decidable_eq n m with
        | inl xeqy := inl (by rewrite xeqy)
        | inr xney := inr (λ h : succ n = succ m, by injection h with xeqy; exact absurd xeqy xney)
        end

    definition not_succ_le_minus_two {n : trunc_index} (H : n .+1 ≤ -2) : empty :=
    by cases H

    protected definition le_trans {n m k : ℕ₋₂} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k :=
    begin
      induction H2 with k H2 IH,
      { exact H1},
      { exact le.step IH}
    end

    definition le_of_succ_le_succ {n m : trunc_index} (H : n.+1 ≤ m.+1) : n ≤ m :=
    begin
      cases H with m H',
      { apply le.tr_refl},
      { exact trunc_index.le_trans (le.step !le.tr_refl) H'}
    end

    theorem not_succ_le_self {n : ℕ₋₂} : ¬n.+1 ≤ n :=
    begin
      induction n with n IH: intro H,
      { exact not_succ_le_minus_two H},
      { exact IH (le_of_succ_le_succ H)}
    end

    protected definition le_antisymm {n m : ℕ₋₂} (H1 : n ≤ m) (H2 : m ≤ n) : n = m :=
    begin
      induction H2 with n H2 IH,
      { reflexivity},
      { exfalso, apply @not_succ_le_self n, exact trunc_index.le_trans H1 H2}
    end

    protected definition le_succ {n m : ℕ₋₂} (H1 : n ≤ m): n ≤ m.+1 :=
    le.step H1

  end trunc_index open trunc_index

  definition weak_order_trunc_index [trans_instance] [reducible] : weak_order trunc_index :=
  weak_order.mk le trunc_index.le_refl @trunc_index.le_trans @trunc_index.le_antisymm

  namespace trunc_index

    /- more theorems about truncation indices -/

    definition zero_add (n : ℕ₋₂) : (0 : ℕ₋₂) + n = n :=
    begin
      cases n with n, reflexivity,
      cases n with n, reflexivity,
      induction n with n IH, reflexivity, exact ap succ IH
    end

    definition add_zero (n : ℕ₋₂) : n + (0 : ℕ₋₂) = n :=
    by reflexivity

    definition succ_add_nat (n : ℕ₋₂) (m : ℕ) : n.+1 + m = (n + m).+1 :=
    by induction m with m IH; reflexivity; exact ap succ IH

    definition nat_add_succ (n : ℕ) (m : ℕ₋₂) : n + m.+1 = (n + m).+1 :=
    begin
      cases m with m, reflexivity,
      cases m with m, reflexivity,
      induction m with m IH, reflexivity, exact ap succ IH
    end

    definition add_nat_succ (n : ℕ₋₂) (m : ℕ) : n + (nat.succ m) = (n + m).+1 :=
    by reflexivity

    definition nat_succ_add (n : ℕ) (m : ℕ₋₂) : (nat.succ n) + m = (n + m).+1 :=
    begin
      cases m with m, reflexivity,
      cases m with m, reflexivity,
      induction m with m IH, reflexivity, exact ap succ IH
    end

    definition sub_two_add_two (n : ℕ₋₂) : sub_two (add_two n) = n :=
    begin
      induction n with n IH,
      { reflexivity},
      { exact ap succ IH}
    end

    definition add_two_sub_two (n : ℕ) : add_two (sub_two n) = n :=
    begin
      induction n with n IH,
      { reflexivity},
      { exact ap nat.succ IH}
    end

    definition of_nat_add_plus_two_of_nat (n m : ℕ) : n +2+ m = of_nat (n + m + 2) :=
    begin
      induction m with m IH,
      { reflexivity},
      { exact ap succ IH}
    end

    definition of_nat_add_of_nat (n m : ℕ) : of_nat n + of_nat m = of_nat (n + m) :=
    begin
      induction m with m IH,
      { reflexivity},
      { exact ap succ IH}
    end

    definition succ_add_plus_two (n m : ℕ₋₂) : n.+1 +2+ m = (n +2+ m).+1 :=
    begin
      induction m with m IH,
      { reflexivity},
      { exact ap succ IH}
    end

    definition add_plus_two_succ (n m : ℕ₋₂) : n +2+ m.+1 = (n +2+ m).+1 :=
    idp

    definition add_succ_succ (n m : ℕ₋₂) : n + m.+2 = n +2+ m :=
    idp

    definition succ_add_succ (n m : ℕ₋₂) : n.+1 + m.+1 = n +2+ m :=
    begin
      cases m with m IH,
      { reflexivity},
      { apply succ_add_plus_two}
    end

    definition succ_succ_add (n m : ℕ₋₂) : n.+2 + m = n +2+ m :=
    begin
      cases m with m IH,
      { reflexivity},
      { exact !succ_add_succ ⬝ !succ_add_plus_two}
    end

    definition succ_sub_two (n : ℕ) : (nat.succ n).-2 = n.-2 .+1 := rfl
    definition sub_two_succ_succ (n : ℕ) : n.-2.+1.+1 = n := rfl
    definition succ_sub_two_succ (n : ℕ) : (nat.succ n).-2.+1 = n := rfl

    definition of_nat_le_of_nat {n m : ℕ} (H : n ≤ m) : (of_nat n ≤ of_nat m) :=
    begin
      induction H with m H IH,
      { apply le.refl},
      { exact trunc_index.le_succ IH}
    end

    definition sub_two_le_sub_two {n m : ℕ} (H : n ≤ m) : n.-2 ≤ m.-2 :=
    begin
      induction H with m H IH,
      { apply le.refl},
      { exact trunc_index.le_succ IH}
    end

    definition add_two_le_add_two {n m : ℕ₋₂} (H : n ≤ m) : add_two n ≤ add_two m :=
    begin
      induction H with m H IH,
      { reflexivity},
      { constructor, exact IH},
    end

    definition le_of_sub_two_le_sub_two {n m : ℕ} (H : n.-2 ≤ m.-2) : n ≤ m :=
    begin
      rewrite [-add_two_sub_two n, -add_two_sub_two m],
      exact add_two_le_add_two H,
    end

    definition le_of_of_nat_le_of_nat {n m : ℕ} (H : of_nat n ≤ of_nat m) : n ≤ m :=
    begin
      apply le_of_sub_two_le_sub_two,
      exact le_of_succ_le_succ (le_of_succ_le_succ H)
    end

  end trunc_index open trunc_index

  variables {A B : Type} {n : ℕ₋₂}

  /- theorems about trunctype -/
  protected definition trunctype.sigma_char.{l} [constructor] (n : ℕ₋₂) :
    (trunctype.{l} n) ≃ (Σ (A : Type.{l}), is_trunc n A) :=
  begin
    fapply equiv.MK,
    { intro A, exact (⟨carrier A, struct A⟩)},
    { intro S, exact (trunctype.mk S.1 S.2)},
    { intro S, induction S with S1 S2, reflexivity},
    { intro A, induction A with A1 A2, reflexivity},
  end

  definition trunctype_eq_equiv [constructor] (n : ℕ₋₂) (A B : n-Type) :
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
      {exfalso, exact not_succ_le_minus_two Hn},
      {apply is_trunc_succ_intro, intro a a',
         fapply @is_trunc_is_equiv_closed_rev _ _ n (ap f)}
  end

  theorem is_trunc_is_retraction_closed (f : A → B) [Hf : is_retraction f]
    (n : ℕ₋₂) [HA : is_trunc n A] : is_trunc n B :=
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

  theorem is_trunc_trunctype [instance] (n : ℕ₋₂) : is_trunc n.+1 (n-Type) :=
  begin
    apply is_trunc_succ_intro, intro X Y,
    fapply is_trunc_equiv_closed,
    { apply equiv.symm, apply trunctype_eq_equiv},
    fapply is_trunc_equiv_closed,
    { apply equiv.symm, apply eq_equiv_equiv},
    induction n,
    { apply @is_contr_of_inhabited_prop,
      { apply is_trunc_is_embedding_closed,
        { apply is_embedding_to_fun} ,
        { reflexivity}},
      { apply equiv_of_is_contr_of_is_contr}},
    { apply is_trunc_is_embedding_closed,
      { apply is_embedding_to_fun},
      { apply minus_one_le_succ}}
  end


  /- theorems about decidable equality and axiom K -/
  theorem is_set_of_axiom_K {A : Type} (K : Π{a : A} (p : a = a), p = idp) : is_set A :=
  is_set.mk _ (λa b p q, eq.rec_on q K p)

  theorem is_set_of_relation.{u} {A : Type.{u}} (R : A → A → Type.{u})
    (mere : Π(a b : A), is_prop (R a b)) (refl : Π(a : A), R a a)
    (imp : Π{a b : A}, R a b → a = b) : is_set A :=
  is_set_of_axiom_K
    (λa p,
      have H2 : transport (λx, R a x → a = x) p (@imp a a) = @imp a a, from !apd,
      have H3 : Π(r : R a a), transport (λx, a = x) p (imp r)
                              = imp (transport (λx, R a x) p r), from
        to_fun (equiv.symm !heq_pi) H2,
      have H4 : imp (refl a) ⬝ p = imp (refl a), from
        calc
          imp (refl a) ⬝ p = transport (λx, a = x) p (imp (refl a)) : transport_eq_r
            ... = imp (transport (λx, R a x) p (refl a)) : H3
            ... = imp (refl a) : is_prop.elim,
      cancel_left (imp (refl a)) H4)

  definition relation_equiv_eq {A : Type} (R : A → A → Type)
    (mere : Π(a b : A), is_prop (R a b)) (refl : Π(a : A), R a a)
    (imp : Π{a b : A}, R a b → a = b) (a b : A) : R a b ≃ a = b :=
  @equiv_of_is_prop _ _ _
    (@is_trunc_eq _ _ (is_set_of_relation R mere refl @imp) a b)
    imp
    (λp, p ▸ refl a)

  local attribute not [reducible]
  theorem is_set_of_double_neg_elim {A : Type} (H : Π(a b : A), ¬¬a = b → a = b)
    : is_set A :=
  is_set_of_relation (λa b, ¬¬a = b) _ (λa n, n idp) H

  section
  open decidable
  --this is proven differently in init.hedberg
  theorem is_set_of_decidable_eq (A : Type) [H : decidable_eq A] : is_set A :=
  is_set_of_double_neg_elim (λa b, by_contradiction)
  end

  theorem is_trunc_of_axiom_K_of_le {A : Type} (n : ℕ₋₂) (H : -1 ≤ n)
    (K : Π(a : A), is_trunc n (a = a)) : is_trunc (n.+1) A :=
  @is_trunc_succ_intro _ _ (λa b, is_trunc_of_imp_is_trunc_of_le H (λp, eq.rec_on p !K))

  theorem is_trunc_succ_of_is_trunc_loop (Hn : -1 ≤ n) (Hp : Π(a : A), is_trunc n (a = a))
    : is_trunc (n.+1) A :=
  begin
    apply is_trunc_succ_intro, intros a a',
    apply is_trunc_of_imp_is_trunc_of_le Hn, intro p,
    induction p, apply Hp
  end

  theorem is_prop_iff_is_contr {A : Type} (a : A) :
    is_prop A ↔ is_contr A :=
  iff.intro (λH, is_contr.mk a (is_prop.elim a)) _

  theorem is_trunc_succ_iff_is_trunc_loop (A : Type) (Hn : -1 ≤ n) :
    is_trunc (n.+1) A ↔ Π(a : A), is_trunc n (a = a) :=
  iff.intro _ (is_trunc_succ_of_is_trunc_loop Hn)

  theorem is_trunc_iff_is_contr_loop_succ (n : ℕ) (A : Type)
    : is_trunc n A ↔ Π(a : A), is_contr (Ω[succ n](pointed.Mk a)) :=
  begin
    revert A, induction n with n IH,
    { intro A, esimp [iterated_ploop_space], transitivity _,
      { apply is_trunc_succ_iff_is_trunc_loop, apply le.refl},
      { apply pi_iff_pi, intro a, esimp, apply is_prop_iff_is_contr, reflexivity}},
    { intro A, esimp [iterated_ploop_space],
      transitivity _,
      { apply @is_trunc_succ_iff_is_trunc_loop @n, esimp, apply minus_one_le_succ},
      apply pi_iff_pi, intro a, transitivity _, apply IH,
      transitivity _, apply pi_iff_pi, intro p,
      rewrite [iterated_loop_space_loop_irrel n p], apply iff.refl, esimp,
      apply imp_iff, reflexivity}
  end

  theorem is_trunc_iff_is_contr_loop (n : ℕ) (A : Type)
    : is_trunc (n.-2.+1) A ↔ (Π(a : A), is_contr (Ω[n](pointed.Mk a))) :=
  begin
    induction n with n,
    { esimp [sub_two,iterated_ploop_space], apply iff.intro,
        intro H a, exact is_contr_of_inhabited_prop a,
        intro H, apply is_prop_of_imp_is_contr, exact H},
    { apply is_trunc_iff_is_contr_loop_succ},
  end

  theorem is_contr_loop_of_is_trunc (n : ℕ) (A : Type*) [H : is_trunc (n.-2.+1) A] :
    is_contr (Ω[n] A) :=
  begin
    induction A,
    apply iff.mp !is_trunc_iff_is_contr_loop H
  end

  theorem is_trunc_loop_of_is_trunc (n : ℕ₋₂) (k : ℕ) (A : Type*) [H : is_trunc n A] :
    is_trunc n (Ω[k] A) :=
  begin
    induction k with k IH,
    { exact H},
    { apply is_trunc_eq}
  end

end is_trunc open is_trunc is_trunc.trunc_index

namespace trunc
  variable {A : Type}

  protected definition code (n : ℕ₋₂) (aa aa' : trunc n.+1 A) : n-Type :=
  trunc.rec_on aa (λa, trunc.rec_on aa' (λa', trunctype.mk' n (trunc n (a = a'))))

  protected definition encode (n : ℕ₋₂) (aa aa' : trunc n.+1 A) : aa = aa' → trunc.code n aa aa' :=
  begin
    intro p, induction p, induction aa with a, esimp [trunc.code,trunc.rec_on], exact (tr idp)
  end

  protected definition decode (n : ℕ₋₂) (aa aa' : trunc n.+1 A) : trunc.code n aa aa' → aa = aa' :=
  begin
    induction aa' with a', induction aa with a,
    esimp [trunc.code, trunc.rec_on], intro x,
    induction x with p, exact ap tr p,
  end

  definition trunc_eq_equiv [constructor] (n : ℕ₋₂) (aa aa' : trunc n.+1 A)
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

  definition tr_eq_tr_equiv [constructor] (n : ℕ₋₂) (a a' : A)
    : (tr a = tr a' :> trunc n.+1 A) ≃ trunc n (a = a') :=
  !trunc_eq_equiv

  definition is_trunc_trunc_of_is_trunc [instance] [priority 500] (A : Type)
    (n m : ℕ₋₂) [H : is_trunc n A] : is_trunc n (trunc m A) :=
  begin
    revert A m H, eapply (trunc_index.rec_on n),
    { clear n, intro A m H, apply is_contr_equiv_closed,
      { apply equiv.symm, apply trunc_equiv, apply (@is_trunc_of_le _ -2), apply minus_two_le} },
    { clear n, intro n IH A m H, induction m with m,
      { apply (@is_trunc_of_le _ -2), apply minus_two_le},
      { apply is_trunc_succ_intro, intro aa aa',
        apply (@trunc.rec_on _ _ _ aa  (λy, !is_trunc_succ_of_is_prop)),
        eapply (@trunc.rec_on _ _ _ aa' (λy, !is_trunc_succ_of_is_prop)),
        intro a a', apply (is_trunc_equiv_closed_rev),
        { apply tr_eq_tr_equiv},
        { exact (IH _ _ _)}}}
  end

  open equiv.ops
  definition unique_choice {P : A → Type} [H : Πa, is_prop (P a)] (f : Πa, ∥ P a ∥) (a : A)
    : P a :=
  !trunc_equiv (f a)

  /- transport over a truncated family -/
  definition trunc_transport {a a' : A} {P : A → Type} (p : a = a') (n : ℕ₋₂) (x : P a)
    : transport (λa, trunc n (P a)) p (tr x) = tr (p ▸ x) :=
  by induction p; reflexivity

  definition trunc_trunc_equiv_left [constructor] (A : Type) (n m : ℕ₋₂) (H : n ≤ m)
    : trunc n (trunc m A) ≃ trunc n A :=
  begin
    note H2 := is_trunc_of_le (trunc n A) H,
    fapply equiv.MK,
    { intro x, induction x with x, induction x with x, exact tr x},
    { intro x, induction x with x, exact tr (tr x)},
    { intro x, induction x with x, reflexivity},
    { intro x, induction x with x, induction x with x, reflexivity}
  end

  definition trunc_trunc_equiv_right [constructor] (A : Type) (n m : ℕ₋₂) (H : n ≤ m)
    : trunc m (trunc n A) ≃ trunc n A :=
  begin
    apply trunc_equiv,
    exact is_trunc_of_le _ H,
  end

  definition image [constructor] {A B : Type} (f : A → B) (b : B) : Prop := ∥ fiber f b ∥

  definition image.mk [constructor] {A B : Type} {f : A → B} {b : B} (a : A) (p : f a = b)
    : image f b :=
  tr (fiber.mk a p)

  -- truncation of pointed types
  definition ptrunc [constructor] (n : ℕ₋₂) (X : Type*) : n-Type* :=
  ptrunctype.mk (trunc n X) _ (tr pt)

  definition ptrunc_functor [constructor] {X Y : Type*} (n : ℕ₋₂) (f : X →* Y)
    : ptrunc n X →* ptrunc n Y :=
  pmap.mk (trunc_functor n f) (ap tr (respect_pt f))

  definition ptrunc_pequiv [constructor] (n : ℕ₋₂) {X Y : Type*} (H : X ≃* Y)
    : ptrunc n X ≃* ptrunc n Y :=
  pequiv_of_equiv (trunc_equiv_trunc n H) (ap tr (respect_pt H))

  definition loop_ptrunc_pequiv [constructor] (n : ℕ₋₂) (A : Type*) :
    Ω (ptrunc (n+1) A) ≃* ptrunc n (Ω A) :=
  pequiv_of_equiv !tr_eq_tr_equiv idp

  definition iterated_loop_ptrunc_pequiv [constructor] (n : ℕ₋₂) (k : ℕ) (A : Type*) :
    Ω[k] (ptrunc (n+k) A) ≃* ptrunc n (Ω[k] A) :=
  begin
    revert n, induction k with k IH: intro n,
    { reflexivity},
    { refine _ ⬝e* loop_ptrunc_pequiv n (Ω[k] A),
      rewrite [iterated_ploop_space_succ], apply loop_pequiv_loop,
      refine _ ⬝e* IH (n.+1),
      rewrite succ_add_nat}
  end

  definition ptrunc_functor_pcompose [constructor] {X Y Z : Type*} (n : ℕ₋₂) (g : Y →* Z)
    (f : X →* Y) : ptrunc_functor n (g ∘* f) ~* ptrunc_functor n g ∘* ptrunc_functor n f :=
  begin
    fapply phomotopy.mk,
    { apply trunc_functor_compose},
    { esimp, refine !idp_con ⬝ _, refine whisker_right !ap_compose'⁻¹ᵖ _ ⬝ _,
      esimp, refine whisker_right (ap_compose' tr g _) _ ⬝ _, exact !ap_con⁻¹},
  end

  definition ptrunc_functor_pid [constructor] (X : Type*) (n : ℕ₋₂) :
    ptrunc_functor n (pid X) ~* pid (ptrunc n X) :=
  begin
    fapply phomotopy.mk,
    { apply trunc_functor_id},
    { reflexivity},
  end

  definition ptrunc_functor_pcast [constructor] {X Y : Type*} (n : ℕ₋₂) (p : X = Y) :
    ptrunc_functor n (pcast p) ~* pcast (ap (ptrunc n) p) :=
  begin
    fapply phomotopy.mk,
    { intro x, esimp, refine !trunc_functor_cast ⬝ _, refine ap010 cast _ x,
      refine !ap_compose'⁻¹ ⬝ !ap_compose'},
    { induction p, reflexivity},
  end

end trunc open trunc

namespace function
  variables {A B : Type}
  definition is_surjective_of_is_equiv [instance] (f : A → B) [H : is_equiv f] : is_surjective f :=
  λb, begin esimp, apply center end

  definition is_equiv_equiv_is_embedding_times_is_surjective [constructor] (f : A → B)
    : is_equiv f ≃ (is_embedding f × is_surjective f) :=
  equiv_of_is_prop (λH, (_, _))
                    (λP, prod.rec_on P (λH₁ H₂, !is_equiv_of_is_surjective_of_is_embedding))

end function
