/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

Declaration of a join as a special case of a pushout
-/

import hit.pushout .susp cubical.cube cubical.squareover

open eq function prod equiv pushout is_trunc bool sigma.ops function

namespace join
  section
  variables (A B C : Type)

  definition join : Type := @pushout (A × B) A B pr1 pr2

  definition jglue {A B : Type} (a : A) (b : B) := @glue (A × B) A B pr1 pr2 (a, b)

  protected definition is_contr [HA : is_contr A] :
    is_contr (join A B) :=
  begin
    fapply is_contr.mk, exact inl (center A),
    intro x, induction x with a b, apply ap inl, apply center_eq,
    apply jglue, induction x with a b, apply pathover_of_tr_eq,
    apply concat, apply transport_eq_Fr, esimp, rewrite ap_id,
    generalize center_eq a, intro p, cases p, apply idp_con,
  end

  protected definition bool : join bool A ≃ susp A :=
  begin
    fapply equiv.MK, intro ba, induction ba with b a,
      induction b, exact susp.south, exact susp.north, exact susp.north,
      induction x with b a, esimp,
      induction b, apply inverse, apply susp.merid, exact a, reflexivity,
    intro s, induction s with m,
      exact inl tt, exact inl ff, exact (jglue tt m) ⬝ (jglue ff m)⁻¹,
    intros, induction b with m, do 2 reflexivity, esimp,
      apply eq_pathover, apply hconcat, apply hdeg_square, apply concat,
      apply ap_compose' (pushout.elim _ _ _), apply concat,
        apply ap (ap (pushout.elim _ _ _)), apply susp.elim_merid, apply ap_con,
      apply hconcat, apply vconcat, apply hdeg_square, apply elim_glue,
        apply hdeg_square, apply ap_inv, esimp,
      apply hconcat, apply hdeg_square, apply concat, apply idp_con,
        apply concat, apply ap inverse, apply elim_glue, apply inv_inv,
      apply hinverse, apply hdeg_square, apply ap_id,
    intro x, induction x with b a, induction b, do 2 reflexivity,
      esimp, apply jglue, induction x with b a, induction b, esimp,
      apply eq_pathover, rewrite ap_id,
      apply eq_hconcat, apply concat, apply ap_compose' (susp.elim _ _ _),
        apply concat, apply ap (ap _) !elim_glue,
        apply concat, apply ap_inv, 
        apply concat, apply ap inverse !susp.elim_merid,
        apply concat, apply con_inv, apply ap (λ x, x ⬝ _) !inv_inv,
      apply square_of_eq_top, apply inverse, 
        apply concat, apply ap (λ x, x ⬝ _) !con.assoc,
        rewrite [con.left_inv, con_idp], apply con.right_inv,
      esimp, apply eq_pathover, rewrite ap_id,
      apply eq_hconcat, apply concat, apply ap_compose' (susp.elim _ _ _),
        apply concat, apply ap (ap _) !elim_glue, esimp, reflexivity,
      apply square_of_eq_top, rewrite idp_con, apply !con.right_inv⁻¹,   
  end

  protected definition swap : join A B → join B A :=
  begin
    intro x, induction x with a b, exact inr a, exact inl b,
    apply !jglue⁻¹
  end

  protected definition swap_involutive (x : join A B) :
    join.swap B A (join.swap A B x) = x :=
  begin
    induction x with a b, do 2 reflexivity,
    induction x with a b, esimp,
    apply eq_pathover, rewrite ap_id,
    apply hdeg_square, esimp[join.swap],
    apply concat, apply ap_compose' (pushout.elim _ _ _),
    krewrite [elim_glue, ap_inv, elim_glue], apply inv_inv,
  end

  protected definition symm : join A B ≃ join B A :=
  begin
    fapply equiv.MK, do 2 apply join.swap,
    do 2 apply join.swap_involutive,
  end

  end

  --This proves that the join operator is associative
  --The proof is more or less ported from Evan Cavallo's agda version
  section switch_assoc
  private definition massage_sq {A : Type} {a₀₀ a₂₀ a₀₂ a₂₂ : A}
    {p₁₀ : a₀₀ = a₂₀} {p₁₂ :  a₀₂ = a₂₂} {p₀₁ : a₀₀ = a₀₂} {p₂₁ : a₂₀ = a₂₂}
    (sq : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀⁻¹ p₀₁⁻¹ (p₂₁ ⬝ p₁₂⁻¹) idp :=
  by induction sq; exact ids

  variables {A B C : Type}

  private definition switch_left : join A B → join (join C B) A :=
  begin
    intro x, induction x with a b, exact inr a, exact inl (inr b), apply !jglue⁻¹,
  end

  private definition switch_coh_fill (a : A) (b : B) (c : C) :
    Σ sq : square (jglue (inl c) a)⁻¹ (ap inl (jglue c b))⁻¹ (ap switch_left (jglue a b)) idp,
      cube hrfl hrfl (hdeg_square !elim_glue) ids 
        sq (eq_hconcat !idp_con⁻¹ (massage_sq (square_Fl_Fl_ap_idp _ _))) :=
  by esimp; apply cube_fill101

  private definition switch_coh (ab : join A B) (c : C) : switch_left ab = inl (inl c) :=
  begin
    induction ab with a b, apply !jglue⁻¹, apply ap inl !jglue⁻¹, induction x with a b,
    apply eq_pathover, refine _ ⬝hp !ap_constant⁻¹, refine _ ⬝vp !ap_inv⁻¹,
    apply (switch_coh_fill _ _ _).1,
  end

  protected definition switch : join (join A B) C → join (join C B) A :=
  begin
    intro x, induction x with ab c, exact switch_left ab, exact inl (inl c),
    induction x with ab c, exact switch_coh ab c,
  end

  private definition switch_inv_left_square (a : A) (b : B) :
    square idp idp (ap (!(@join.switch C) ∘ switch_left) (jglue a b)) (ap inl (jglue a b)) :=
  begin
    refine hdeg_square !ap_compose ⬝h _,
    refine aps join.switch (hdeg_square !elim_glue) ⬝h _, esimp,
    refine hdeg_square !(ap_inv join.switch) ⬝h _,
    refine hrfl⁻¹ʰ⁻¹ᵛ ⬝h _, esimp[join.switch,switch_left,switch_coh],
    refine (hdeg_square !elim_glue)⁻¹ᵛ ⬝h _, esimp,
    refine (hdeg_square !ap_inv)⁻¹ᵛ ⬝h _, apply hdeg_square !inv_inv,
  end

  private definition switch_inv_coh_left (c : C) (a : A) :
    square idp idp (ap !(@join.switch C B) (switch_coh (inl a) c)) (jglue (inl a) c) :=
  begin
    refine hrfl ⬝h _,
    refine 
  end


  end switch_assoc

exit

  protected definition switch_equiv (A B C : Type) :
    join (join A B) C ≃ join (join C B) A :=
  by apply equiv.MK; do 2 apply join.switch_involutive

  protected definition assoc (A B C : Type) :
    join (join A B) C ≃ join A (join B C) :=
  calc join (join A B) C ≃ join (join C B) A : join.switch_equiv
                     ... ≃ join A (join C B) : join.symm
                     ... ≃ join A (join B C) : join.symm

end join
