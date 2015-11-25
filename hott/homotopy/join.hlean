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
  section join_switch
  private definition massage_sq' {A : Type} {a₀₀ a₂₀ a₀₂ a₂₂ : A}
    {p₁₀ : a₀₀ = a₂₀} {p₁₂ :  a₀₂ = a₂₂} {p₀₁ : a₀₀ = a₀₂} {p₂₁ : a₂₀ = a₂₂}
    (sq : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀⁻¹ p₀₁⁻¹ (p₂₁ ⬝ p₁₂⁻¹) idp :=
  by induction sq; exact ids

  private definition massage_sq {A : Type} {a₀₀ a₂₀ a₀₂ : A}
    {p₁₀ : a₀₀ = a₂₀} {p₁₂ :  a₀₂ = a₂₀} {p₀₁ : a₀₀ = a₀₂}
    (sq : square p₁₀ p₁₂ p₀₁ idp) : square p₁₀⁻¹ p₀₁⁻¹ p₁₂⁻¹ idp :=
  !idp_con⁻¹ ⬝ph (massage_sq' sq)

  private definition ap_square_massage {A B : Type} (f : A → B) {a₀₀ a₀₂ a₂₀ : A}
    {p₀₁ : a₀₀ = a₀₂} {p₁₀ : a₀₀ = a₂₀} {p₁₁ : a₂₀ = a₀₂} (sq : square p₀₁ p₁₁ p₁₀ idp) :
    cube (hdeg_square (ap_inv f p₁₁)) ids
         (aps f (massage_sq sq)) (massage_sq (aps f sq))
         (hdeg_square !ap_inv) (hdeg_square !ap_inv) :=
  by apply rec_on_r sq; apply idc

  private definition massage_cube' {A : Type} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ : A}
    {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂} {p₁₂₀ : a₀₂₀ = a₂₂₀}
    {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂} {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂}
    {p₀₂₁ : a₀₂₀ = a₀₂₂} {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
    {s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} {s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
    {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁} {s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
    {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁} {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
    (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
    cube (s₂₁₁ ⬝v s₁₁₂⁻¹ᵛ) vrfl (massage_sq' s₁₀₁) (massage_sq' s₁₂₁) s₁₁₀⁻¹ᵛ s₀₁₁⁻¹ᵛ :=
  by cases c; apply idc

  private definition massage_cube {A : Type} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₀₂₂ : A}
    {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂} {p₁₂₀ : a₀₂₀ = a₂₂₀}
    {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₁₀₂ : a₀₀₂ = a₂₀₀} {p₀₁₂ : a₀₀₂ = a₀₂₂}
    {p₀₂₁ : a₀₂₀ = a₀₂₂} {p₁₂₂ : a₀₂₂ = a₂₂₀}
    {s₁₁₀ : square p₀₁₀ _ _ _} {s₁₁₂ : square p₀₁₂ p₂₁₀ p₁₀₂ p₁₂₂}
    {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁} {s₂₁₁ : square p₂₁₀ p₂₁₀ idp idp}
    {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ idp} {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ idp}
    (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
    cube s₁₁₂⁻¹ᵛ vrfl (massage_sq s₁₀₁) (massage_sq s₁₂₁) s₁₁₀⁻¹ᵛ s₀₁₁⁻¹ᵛ :=
  begin
    unfold massage_sq, exact sorry
  end

  private definition massage_massage {A : Type} {a₀₀ a₀₂ a₂₀ : A}
    {p₀₁ : a₀₀ = a₀₂} {p₁₀ : a₀₀ = a₂₀} {p₁₁ : a₂₀  = a₀₂} (sq : square p₀₁ p₁₁ p₁₀ idp) :
    cube (hdeg_square !inv_inv) ids (massage_sq (massage_sq sq))
      sq (hdeg_square !inv_inv) (hdeg_square !inv_inv) :=
  by apply rec_on_r sq; apply idc

  private definition square_Flr_ap_idp_cube {A B : Type} {b : B} {f : A → B}
    {p₁ p₂ : Π a, f a = b} (α : Π a, p₁ a = p₂ a) {a₁ a₂ : A} (q : a₁ = a₂) :
    cube hrfl hrfl (square_Flr_ap_idp p₁ q) (square_Flr_ap_idp p₂ q) 
      (hdeg_square (α _)) (hdeg_square (α _)) :=
  begin
    cases q, esimp[square_Flr_ap_idp], apply deg3_cube, apply refl,
  end

  variables {A B C : Type}

  private definition switch_left [reducible] : join A B → join (join C B) A :=
  begin
    intro x, induction x with a b, exact inr a, exact inl (inr b), apply !jglue⁻¹,
  end

  private definition switch_coh_fill (a : A) (b : B) (c : C) :
    Σ sq : square (jglue (inl c) a)⁻¹ (ap inl (jglue c b))⁻¹ (ap switch_left (jglue a b)) idp,
      cube (hdeg_square !elim_glue) ids sq (massage_sq !square_Flr_ap_idp) hrfl hrfl :=
  by esimp; apply cube_fill101

  private definition switch_coh (ab : join A B) (c : C) : switch_left ab = inl (inl c) :=
  begin
    induction ab with a b, apply !jglue⁻¹, apply (ap inl !jglue)⁻¹, induction x with a b,
    apply eq_pathover, refine _ ⬝hp !ap_constant⁻¹,
    apply !switch_coh_fill.1,
  end

  protected definition switch [reducible] : join (join A B) C → join (join C B) A :=
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
    refine hrfl⁻¹ᵛ ⬝h _, apply hdeg_square !inv_inv,
  end

  private definition switch_inv_coh_left (c : C) (a : A) :
    square idp idp (ap !(@join.switch C B) (switch_coh (inl a) c)) (jglue (inl a) c) :=
  begin
    refine hrfl ⬝h _,
    refine aps join.switch hrfl ⬝h _, esimp[switch_coh],
    refine hdeg_square !ap_inv ⬝h _,
    refine hrfl⁻¹ʰ⁻¹ᵛ ⬝h _, esimp[join.switch,switch_left],
    refine (hdeg_square !elim_glue)⁻¹ᵛ ⬝h _,
    refine hrfl⁻¹ᵛ ⬝h _, apply hdeg_square !inv_inv,
  end

  private definition switch_inv_coh_right (c : C) (b : B) :
    square idp idp (ap !(@join.switch _ _ A) (switch_coh (inr b) c)) (jglue (inr b) c) :=
  begin
    refine hrfl ⬝h _,
    refine aps join.switch hrfl ⬝h _, esimp[switch_coh],
    refine hdeg_square !ap_inv ⬝h _,
    refine (hdeg_square !ap_compose)⁻¹ʰ⁻¹ᵛ ⬝h _,
    refine hrfl⁻¹ᵛ ⬝h _, esimp[join.switch,switch_left],
    refine (hdeg_square !elim_glue)⁻¹ᵛ ⬝h _, apply hdeg_square !inv_inv,
  end

  private definition switch_inv_left (ab : join A B) :
    !(@join.switch C) (join.switch (inl ab)) = inl ab :=
  begin
    induction ab with a b, do 2 reflexivity,
    induction x with a b, apply eq_pathover, exact !switch_inv_left_square,
  end

  section
  variables (a : A) (b : B) (c : C)

  private definition switch_inv_cube_aux1 {A B C : Type} {b : B} {f : A → B} (h : B → C)
    (g : Π a, f a = b) {x y : A} (p : x = y) :
    cube (hdeg_square (ap_compose h f p)) ids (square_Flr_ap_idp (λ a, ap h (g a)) p)
    (aps h (square_Flr_ap_idp _ _)) hrfl hrfl :=
  begin
    cases p, esimp[square_Flr_ap_idp], apply deg2_cube,
    cases (g x), reflexivity,
  end

  private definition switch_inv_cube_aux2 {A B : Type} {b : B} {f : A → B}
    (g : Π a, f a = b) {x y : A} (p : x = y) {sq : square (g x) (g y) (ap f p) idp}
    (q : apdo g p = eq_pathover (sq ⬝hp !ap_constant⁻¹)) : square_Flr_ap_idp _ _ = sq :=
  begin
    cases p, esimp at *, exact sorry
  end

  --set_option pp.implicit true

  private definition switch_inv_cube (a : A) (b : B) (c : C) :
    cube (switch_inv_left_square a b) ids (square_Flr_ap_idp _ _)
    (square_Flr_ap_idp _ _) (switch_inv_coh_left c a) (switch_inv_coh_right c b) :=
  begin
    esimp [switch_inv_coh_left, switch_inv_coh_right, switch_inv_left_square],
    apply cube_concat2, apply switch_inv_cube_aux1,
    apply cube_concat2, apply cube_transport101, apply inverse, 
      apply ap (λ x, aps join.switch x), apply switch_inv_cube_aux2, apply rec_glue,
      apply apc, apply (switch_coh_fill a b c).2,
    apply cube_concat2, esimp, apply ap_square_massage,
    apply cube_concat2, apply massage_cube, apply cube_inverse2, apply switch_inv_cube_aux1,
    apply cube_concat2, apply massage_cube, apply square_Flr_ap_idp_cube,
    apply cube_concat2, apply massage_cube, apply cube_transport101,
      apply inverse, apply switch_inv_cube_aux2,
      esimp[switch_coh], apply rec_glue, apply (switch_coh_fill c b a).2,
    apply massage_massage,
  end

  end

  private definition pathover_of_triangle_cube {A B : Type} {b₀ b₁ : A → B}
    {b : B} {p₀₁ : Π a, b₀ a = b₁ a} {p₀ : Π a, b₀ a = b} {p₁ : Π a, b₁ a = b}
    {x y : A} {q : x = y} {sqx : square (p₀₁ x) idp (p₀ x) (p₁ x)}
    {sqy : square (p₀₁ y) idp (p₀ y) (p₁ y)}
    (c : cube (natural_square_tr _ _) ids (square_Flr_ap_idp p₀ q) (square_Flr_ap_idp p₁ q)
       sqx sqy) :
    sqx =[q] sqy :=
  begin
    cases q, esimp [square_Flr_ap_idp] at *,
    apply pathover_of_eq_tr, esimp, apply eq_of_deg12_cube, exact c,
  end

  private definition pathover_of_ap_ap_square {A : Type} {x y : A} {p : x = y}
    (g : B → A) (f : A → B) {u : g (f x) = x} {v : g (f y) = y}
    (sq : square (ap g (ap f p)) p u v) : u =[p] v :=
  by cases p; apply eq_pathover; apply transpose; exact sq


  private definition hdeg_square_idp {A : Type} {a a' : A} {p : a = a'} :
    hdeg_square (refl p) = hrfl :=
  by cases p; reflexivity

  private definition vdeg_square_idp {A : Type} {a a' : A} {p : a = a'} :
    vdeg_square (refl p) = vrfl :=
  by cases p; reflexivity

  private definition natural_square_tr_beta {A B : Type} {f₁ f₂ : A → B}
    (p : Π a, f₁ a = f₂ a) {x y : A} (q : x = y) {sq : square (p x) (p y) (ap f₁ q) (ap f₂ q)}
    (e : apdo p q = eq_pathover sq) :
    natural_square_tr p q = sq :=
  begin
    cases q, esimp at *,
    apply concat, apply inverse, apply vdeg_square_idp,
    assert H : refl (p y) = eq_of_vdeg_square sq,
    { exact sorry },
    apply concat, apply ap vdeg_square, exact H,
    apply is_equiv.left_inv (equiv.to_fun !vdeg_square_equiv),
  end

  private definition switch_inv_coh (c : C) (k : join A B) :
    square (switch_inv_left k) idp (ap join.switch (switch_coh k c)) (jglue k c) :=
  begin
    induction k, apply switch_inv_coh_left, apply switch_inv_coh_right,
    refine pathover_of_triangle_cube _,
    induction x with [a, b], esimp, apply cube_transport011,
    apply inverse, rotate 1, apply switch_inv_cube,
    apply natural_square_tr_beta, apply rec_glue,
  end

  protected definition switch_involutive (x : join (join A B) C) :
    join.switch (join.switch x) = x :=
  begin
    induction x, apply switch_inv_left, reflexivity,
    apply pathover_of_ap_ap_square join.switch join.switch,
    induction x with [k, c], krewrite elim_glue, esimp,
    apply transpose, exact !switch_inv_coh,
  end

  end join_switch 

  protected definition switch_equiv (A B C : Type) :
    join (join A B) C ≃ join (join C B) A :=
  by apply equiv.MK; do 2 apply join.switch_involutive

  protected definition assoc (A B C : Type) :
    join (join A B) C ≃ join A (join B C) :=
  calc join (join A B) C ≃ join (join C B) A : join.switch_equiv
                     ... ≃ join A (join C B) : join.symm
                     ... ≃ join A (join B C) : join.symm

end join
