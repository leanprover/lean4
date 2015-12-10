/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Coherence conditions for operations on pathovers
-/

open function equiv

namespace eq

  variables {A A' A'' : Type} {B B' : A → Type} {B'' : A' → Type} {C : Π⦃a⦄, B a → Type}
            {a a₂ a₃ a₄ : A} {p p' p'' : a = a₂} {p₂ p₂' : a₂ = a₃} {p₃ : a₃ = a₄} {p₁₃ : a = a₃}
            {a' : A'}
            {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
            {c : C b} {c₂ : C b₂}

  definition pathover_ap_id (q : b =[p] b₂) : pathover_ap B id q = change_path (ap_id p)⁻¹ q :=
  by induction q; reflexivity

  definition pathover_ap_compose (B : A'' → Type) (g : A' → A'') (f : A → A')
    {b : B (g (f a))} {b₂ : B (g (f a₂))} (q : b =[p] b₂) : pathover_ap B (g ∘ f) q
      = change_path (ap_compose g f p)⁻¹ (pathover_ap B g (pathover_ap (B ∘ g) f q)) :=
  by induction q; reflexivity

  definition pathover_ap_compose_rev (B : A'' → Type) (g : A' → A'') (f : A → A')
    {b : B (g (f a))} {b₂ : B (g (f a₂))} (q : b =[p] b₂) :
    pathover_ap B g (pathover_ap (B ∘ g) f q)
      = change_path (ap_compose g f p) (pathover_ap B (g ∘ f) q) :=
  by induction q; reflexivity

  definition pathover_of_tr_eq_idp (r : b = b') : pathover_of_tr_eq r = pathover_idp_of_eq r :=
  idp

  definition pathover_of_tr_eq_eq_concato (r : p ▸ b = b₂)
    : pathover_of_tr_eq r = pathover_tr p b ⬝o pathover_idp_of_eq r :=
  by induction r; induction p; reflexivity

  definition apo011_eq_apo11_apdo (f : Πa, B a → A') (p : a = a₂) (q : b =[p] b₂)
      : apo011 f p q = eq_of_pathover (apo11 (apdo f p) q) :=
  by induction q; reflexivity

  definition change_path_con (q : p = p') (q' : p' = p'') (r : b =[p] b₂) :
    change_path (q ⬝ q') r = change_path q' (change_path q r) :=
  by induction q; induction q'; reflexivity

  definition change_path_invo (q : p = p') (r : b =[p] b₂) :
    change_path (inverse2 q) r⁻¹ᵒ = (change_path q r)⁻¹ᵒ :=
  by induction q; reflexivity

  definition change_path_cono (q : p = p') (q₂ : p₂ = p₂') (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃):
    change_path (q ◾ q₂) (r ⬝o r₂) = change_path q r ⬝o change_path q₂ r₂ :=
  by induction q; induction q₂; reflexivity

  definition pathover_of_pathover_ap_invo (B' : A' → Type) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[ap f p] b₂) :
    pathover_of_pathover_ap B' f (change_path (ap_inv f p)⁻¹ q⁻¹ᵒ) =
      (pathover_of_pathover_ap B' f q)⁻¹ᵒ:=
  by induction p; eapply idp_rec_on q; reflexivity

  definition pathover_of_pathover_ap_cono (B' : A' → Type) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} {b₃ : B' (f a₃)} (q : b =[ap f p] b₂) (q₂ : b₂ =[ap f p₂] b₃) :
    pathover_of_pathover_ap B' f (change_path (ap_con f p p₂)⁻¹ (q ⬝o q₂)) =
      pathover_of_pathover_ap B' f q ⬝o pathover_of_pathover_ap B' f q₂ :=
  by induction p; induction p₂; eapply idp_rec_on q; eapply idp_rec_on q₂; reflexivity

  definition pathover_ap_pathover_of_pathover_ap (P : A'' → Type) (g : A' → A'') (f : A → A')
    {p : a = a₂} {b : P (g (f a))} {b₂ : P (g (f a₂))} (q : b =[ap f p] b₂) :
    pathover_ap P (g ∘ f) (pathover_of_pathover_ap (P ∘ g) f q) =
    change_path (ap_compose g f p)⁻¹ (pathover_ap P g q) :=
  by induction p; eapply (idp_rec_on q); reflexivity

  definition change_path_pathover_of_pathover_ap (B' : A' → Type) (f : A → A') {p p' : a = a₂}
    (r : p = p') {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[ap f p] b₂) :
    change_path r (pathover_of_pathover_ap B' f q) =
      pathover_of_pathover_ap B' f (change_path (ap02 f r) q) :=
  by induction r; reflexivity

  definition pathover_ap_change_path (B' : A' → Type) (f : A → A') {p p' : a = a₂}
    (r : p = p') {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) :
    pathover_ap B' f (change_path r q) = change_path (ap02 f r) (pathover_ap B' f q) :=
  by induction r; reflexivity

  definition change_path_equiv [constructor] (b : B a) (b₂ : B a₂) (q : p = p')
    : (b =[p] b₂) ≃ (b =[p'] b₂) :=
  begin
    fapply equiv.MK,
    { exact change_path q},
    { exact change_path q⁻¹},
    { intro r, induction q, reflexivity},
    { intro r, induction q, reflexivity},
  end

  definition apdo_ap {B : A' → Type} (g : Πb, B b) (f : A → A') (p : a = a₂)
    :  apdo g (ap f p) = pathover_ap B f (apdo (λx, g (f x)) p)  :=
  by induction p; reflexivity

  definition apdo_eq_apdo_ap {B : A' → Type} (g : Πb, B b) (f : A → A') (p : a = a₂)
    : apdo (λx, g (f x)) p = pathover_of_pathover_ap B f (apdo g (ap f p)) :=
  by induction p; reflexivity

  definition ap_compose_ap02_constant {A B C : Type} {a a' : A} (p : a = a') (b : B) (c : C) :
  ap_compose (λc, b) (λa, c) p ⬝ ap02 (λc, b) (ap_constant p c) = ap_constant p b :=
  by induction p; reflexivity

  theorem apdo_constant (b : B'' a') (p : a = a) :
    pathover_ap B'' (λa, a') (apdo (λa, b) p) = change_path (ap_constant p a')⁻¹ idpo :=
  begin
    rewrite [apdo_eq_apdo_ap _ _ p],
    let y := !change_path_of_pathover (apdo (apdo id) (ap_constant p b))⁻¹ᵒ,
    rewrite -y, esimp,
    refine !pathover_ap_pathover_of_pathover_ap ⬝ _,
    rewrite pathover_ap_change_path,
    rewrite -change_path_con, apply ap (λx, change_path x idpo),
    unfold ap02, rewrite [ap_inv,-con_inv], apply inverse2,
    apply ap_compose_ap02_constant
  end

  definition apdo_change_path {B : A → Type} {a a₂ : A} (f : Πa, B a) {p p' : a = a₂} (s : p = p')
    : apdo f p' = change_path s (apdo f p) :=
  by induction s; reflexivity

  definition cono_invo_eq_idpo {q q' : b =[p] b₂} (r : q = q')
    : change_path (con.right_inv p) (q ⬝o q'⁻¹ᵒ) = idpo :=
  by induction r; induction q; reflexivity

end eq
