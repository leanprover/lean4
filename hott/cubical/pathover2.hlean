/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Coherence conditions for operations on pathovers
-/

open function

namespace eq

  variables {A A' A'' : Type} {a a' a₂ : A} (B : A → Type) {p : a = a₂}
    {b b' : B a} {b₂ : B a₂}

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

  definition apdo_eq_apdo_ap {B : A' → Type} (g : Πb, B b) (f : A → A') (p : a = a')
    : apdo (λx, g (f x)) p = pathover_of_pathover_ap B f (apdo g (ap f p)) :=
  by induction p; reflexivity

  definition pathover_of_tr_eq_idp (r : b = b') : pathover_of_tr_eq r = pathover_idp_of_eq r :=
  idp

  definition pathover_of_tr_eq_eq_concato (r : p ▸ b = b₂)
    : pathover_of_tr_eq r = pathover_tr p b ⬝o pathover_idp_of_eq r :=
  by induction r; induction p; reflexivity

  definition apo011_eq_apo11_apdo (f : Πa, B a → A') (p : a = a₂) (q : b =[p] b₂)
      : apo011 f p q = eq_of_pathover (apo11 (apdo f p) q) :=
  by induction q; reflexivity

end eq
