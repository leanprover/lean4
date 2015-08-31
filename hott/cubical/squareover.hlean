/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Squareovers
-/

import .square

open eq equiv is_equiv equiv.ops

namespace eq

  -- we give the argument B explicitly, because Lean would find (λa, B a) by itself, which
  -- makes the type uglier (of course the two terms are definitionally equal)
  inductive squareover {A : Type} (B : A → Type) {a₀₀ : A} {b₀₀ : B a₀₀} :
    Π{a₂₀ a₀₂ a₂₂ : A}
     {p₁₀ : a₀₀ = a₂₀} {p₁₂ : a₀₂ = a₂₂} {p₀₁ : a₀₀ = a₀₂} {p₂₁ : a₂₀ = a₂₂}
     (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
     {b₂₀ : B a₂₀} {b₀₂ : B a₀₂} {b₂₂ : B a₂₂}
     (q₁₀ : pathover B b₀₀ p₁₀ b₂₀) (q₁₂ : pathover B b₀₂ p₁₂ b₂₂)
     (q₀₁ : pathover B b₀₀ p₀₁ b₀₂) (q₂₁ : pathover B b₂₀ p₂₁ b₂₂),
     Type :=
  idsquareo : squareover B ids idpo idpo idpo idpo


  variables {A A' : Type} {B : A → Type}
            {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ : A}
            /-a₀₀-/ {p₁₀ : a₀₀ = a₂₀} /-a₂₀-/ {p₃₀ : a₂₀ = a₄₀} /-a₄₀-/
       {p₀₁ : a₀₀ = a₀₂} /-s₁₁-/ {p₂₁ : a₂₀ = a₂₂} /-s₃₁-/ {p₄₁ : a₄₀ = a₄₂}
            /-a₀₂-/ {p₁₂ : a₀₂ = a₂₂} /-a₂₂-/ {p₃₂ : a₂₂ = a₄₂} /-a₄₂-/
       {p₀₃ : a₀₂ = a₀₄} /-s₁₃-/ {p₂₃ : a₂₂ = a₂₄} /-s₃₃-/ {p₄₃ : a₄₂ = a₄₄}
            /-a₀₄-/ {p₁₄ : a₀₄ = a₂₄} /-a₂₄-/ {p₃₄ : a₂₄ = a₄₄} /-a₄₄-/
            {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁}
            {b₀₀ : B a₀₀} {b₂₀ : B a₂₀} {b₄₀ : B a₄₀}
            {b₀₂ : B a₀₂} {b₂₂ : B a₂₂} {b₄₂ : B a₄₂}
            {b₀₄ : B a₀₄} {b₂₄ : B a₂₄} {b₄₄ : B a₄₄}
            /-b₀₀-/ {q₁₀ : b₀₀ =[p₁₀] b₂₀} /-b₂₀-/ {q₃₀ : b₂₀ =[p₃₀] b₄₀} /-b₄₀-/
   {q₀₁ : b₀₀ =[p₀₁] b₀₂} /-t₁₁-/ {q₂₁ : b₂₀ =[p₂₁] b₂₂} /-t₃₁-/ {q₄₁ : b₄₀ =[p₄₁] b₄₂}
            /-b₀₂-/ {q₁₂ : b₀₂ =[p₁₂] b₂₂} /-b₂₂-/ {q₃₂ : b₂₂ =[p₃₂] b₄₂} /-b₄₂-/
   {q₀₃ : b₀₂ =[p₀₃] b₀₄} /-t₁₃-/ {q₂₃ : b₂₂ =[p₂₃] b₂₄} /-t₃₃-/ {q₄₃ : b₄₂ =[p₄₃] b₄₄}
            /-b₀₄-/ {q₁₄ : b₀₄ =[p₁₄] b₂₄} /-b₂₄-/ {q₃₄ : b₂₄ =[p₃₄] b₄₄} /-b₄₄-/

  definition squareo := @squareover A B a₀₀
  definition idsquareo [reducible] [constructor] (b₀₀ : B a₀₀) := @squareover.idsquareo A B a₀₀ b₀₀
  definition idso      [reducible] [constructor]               := @squareover.idsquareo A B a₀₀ b₀₀

  definition apds (f : Πa, B a) (s : square p₁₀ p₁₂ p₀₁ p₂₁)
    : squareover B s (apdo f p₁₀) (apdo f p₁₂) (apdo f p₀₁) (apdo f p₂₁) :=
  square.rec_on s idso

  definition vrflo : squareover B vrfl q₁₀ q₁₀ idpo idpo :=
  by induction q₁₀; exact idso

  definition hrflo : squareover B hrfl idpo idpo q₁₀ q₁₀ :=
  by induction q₁₀; exact idso

  definition vdeg_squareover {q₁₀' : b₀₀ =[p₁₀] b₂₀} (r : q₁₀ = q₁₀')
    : squareover B vrfl q₁₀ q₁₀' idpo idpo :=
  by induction r;exact vrflo

  definition hdeg_squareover {q₀₁' : b₀₀ =[p₀₁] b₀₂} (r : q₀₁ = q₀₁')
    : squareover B hrfl idpo idpo q₀₁ q₀₁' :=
  by induction r; exact hrflo

  -- relating squareovers to squares
  definition square_of_squareover (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) :
    square (!con_tr ⬝ ap (λa, p₂₁ ▸ a) (tr_eq_of_pathover q₁₀))
           (tr_eq_of_pathover q₁₂)
           (ap (λq, q ▸ b₀₀) (eq_of_square s₁₁) ⬝ !con_tr ⬝ ap (λa, p₁₂ ▸ a) (tr_eq_of_pathover q₀₁))
           (tr_eq_of_pathover q₂₁) :=
  by induction t₁₁; esimp; constructor
/-
  definition squareover_of_square
    (q : square (!con_tr ⬝ ap (λa, p₂₁ ▸ a) (tr_eq_of_pathover q₁₀))
           (tr_eq_of_pathover q₁₂)
           (ap (λq, q ▸ b₀₀) (eq_of_square s₁₁) ⬝ !con_tr ⬝ ap (λa, p₁₂ ▸ a) (tr_eq_of_pathover q₀₁))
           (tr_eq_of_pathover q₂₁))
    : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁ :=
  sorry
-/

  definition square_of_squareover_ids {b₀₀ b₀₂ b₂₀ b₂₂ : B a}
    (t : b₀₀ = b₂₀) (b : b₀₂ = b₂₂) (l : b₀₀ = b₀₂) (r : b₂₀ = b₂₂)
    (so : squareover B ids (pathover_idp_of_eq t)
                           (pathover_idp_of_eq b)
                           (pathover_idp_of_eq l)
                           (pathover_idp_of_eq r)) : square t b l r :=
  begin
    let H := square_of_squareover so,  -- use apply ... in
    rewrite [▸* at H,+idp_con at H,+ap_id at H,↑pathover_idp_of_eq at H],
    rewrite [+to_right_inv !(pathover_equiv_tr_eq (refl a)) at H],
    exact H
  end

  definition squareover_ids_of_square {b₀₀ b₀₂ b₂₀ b₂₂ : B a}
    (t : b₀₀ = b₂₀) (b : b₀₂ = b₂₂) (l : b₀₀ = b₀₂) (r : b₂₀ = b₂₂) (q : square t b l r)
    : squareover B ids (pathover_idp_of_eq t)
                       (pathover_idp_of_eq b)
                       (pathover_idp_of_eq l)
                       (pathover_idp_of_eq r) :=
  square.rec_on q idso

  -- relating pathovers to squareovers
  definition pathover_of_squareover' (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁)
    : q₁₀ ⬝o q₂₁ =[eq_of_square s₁₁] q₀₁ ⬝o q₁₂ :=
  by induction t₁₁; constructor

  definition pathover_of_squareover {s : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂}
    (t₁₁ : squareover B (square_of_eq s) q₁₀ q₁₂ q₀₁ q₂₁)
    : q₁₀ ⬝o q₂₁ =[s] q₀₁ ⬝o q₁₂ :=
  begin
    revert s t₁₁, refine equiv_rect' !square_equiv_eq⁻¹ᵉ (λa b, squareover B b _ _ _ _ → _) _,
    intro s, exact pathover_of_squareover'
  end

  definition squareover_of_pathover {s : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂}
    (r : q₁₀ ⬝o q₂₁ =[s] q₀₁ ⬝o q₁₂) : squareover B (square_of_eq s) q₁₀ q₁₂ q₀₁ q₂₁ :=
  by induction q₁₂; esimp [concato] at r;induction r;induction q₂₁;induction q₁₀;constructor

  definition pathover_top_of_squareover (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁)
    : q₁₀ =[eq_top_of_square s₁₁] q₀₁ ⬝o q₁₂ ⬝o q₂₁⁻¹ᵒ :=
  by induction t₁₁; constructor

  definition squareover_of_pathover_top {s : p₁₀ = p₀₁ ⬝ p₁₂ ⬝ p₂₁⁻¹}
  (r : q₁₀ =[s] q₀₁ ⬝o q₁₂ ⬝o q₂₁⁻¹ᵒ)
    : squareover B (square_of_eq_top s) q₁₀ q₁₂ q₀₁ q₂₁ :=
  by induction q₂₁; induction q₁₂; esimp at r;induction r;induction q₁₀;constructor

  definition pathover_of_hdeg_squareover {p₀₁' : a₀₀ = a₀₂} {r : p₀₁ = p₀₁'} {q₀₁' : b₀₀ =[p₀₁'] b₀₂}
    (t : squareover B (hdeg_square r) idpo idpo q₀₁ q₀₁') : q₀₁ =[r] q₀₁' :=
  by induction r; induction q₀₁'; exact (pathover_of_squareover' t)⁻¹ᵒ

  definition pathover_of_vdeg_squareover {p₁₀' : a₀₀ = a₂₀} {r : p₁₀ = p₁₀'} {q₁₀' : b₀₀ =[p₁₀'] b₂₀}
    (t : squareover B (vdeg_square r) q₁₀ q₁₀' idpo idpo) : q₁₀ =[r] q₁₀' :=
  by induction r; induction q₁₀'; exact pathover_of_squareover' t

  definition squareover_of_eq_top (r : change_path (eq_top_of_square s₁₁) q₁₀ = q₀₁ ⬝o q₁₂ ⬝o q₂₁⁻¹ᵒ)
    : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁ :=
  begin
    induction s₁₁, revert q₁₂ q₁₀ r,
    eapply idp_rec_on q₂₁, clear q₂₁,
    intro q₁₂,
    eapply idp_rec_on q₁₂, clear q₁₂,
    esimp, intros,
    induction r, eapply idp_rec_on q₁₀,
    constructor
  end

  definition eq_top_of_squareover (r : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁)
    : change_path (eq_top_of_square s₁₁) q₁₀ = q₀₁ ⬝o q₁₂ ⬝o q₂₁⁻¹ᵒ :=
  by induction r; reflexivity

  /-
  definition squareover_equiv_pathover (q₁₀ : b₀₀ =[p₁₀] b₂₀) (q₁₂ : b₀₂ =[p₁₂] b₂₂)
    (q₀₁ : b₀₀ =[p₀₁] b₀₂) (q₂₁ : b₂₀ =[p₂₁] b₂₂)
    : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁ ≃ q₁₀ ⬝o q₂₁ =[eq_of_square s₁₁] q₀₁ ⬝o q₁₂ :=
  begin
    fapply equiv.MK,
    { exact pathover_of_squareover},
    { intro r, rewrite [-to_left_inv !square_equiv_eq s₁₁], apply squareover_of_pathover, exact r},
    { intro r, }, --need characterization of squareover lying over ids.
    { intro s, induction s, apply idp},
  end
  -/

  definition eq_of_vdeg_squareover {q₁₀' : b₀₀ =[p₁₀] b₂₀}
    (p : squareover B vrfl q₁₀ q₁₀' idpo idpo) : q₁₀ = q₁₀' :=
  begin
    let H := square_of_squareover p,  -- use apply ... in
    induction p₁₀, -- if needed we can remove this induction and use con_tr_idp in types/eq2
    rewrite [▸* at H,idp_con at H,+ap_id at H],
    let H' := eq_of_vdeg_square H,
    exact eq_of_fn_eq_fn !pathover_equiv_tr_eq H'
  end

  -- definition vdeg_tr_squareover {q₁₂ : p₀₁ ▸ b₀₀ =[p₁₂] p₂₁ ▸ b₂₀} (r : q₁₀ =[_] q₁₂)
  --   : squareover B s₁₁ q₁₀ q₁₂ !pathover_tr !pathover_tr :=
  -- by induction p;exact vrflo

  /- charcaterization of pathovers in pathovers -/
  -- in this version the fibration (B) of the pathover does not depend on the variable a
  definition pathover_pathover {a' a₂' : A'} {p : a' = a₂'} {f g : A' → A}
    {b : Πa, B (f a)} {b₂ : Πa, B (g a)} {q : Π(a' : A'), f a' = g a'}
    (r : pathover B (b a') (q a') (b₂ a'))
    (r₂ : pathover B (b a₂') (q a₂') (b₂ a₂'))
    (s : squareover B (natural_square_tr q p) r r₂
                      (pathover_ap B f (apdo b p)) (pathover_ap B g (apdo b₂ p)))
    : pathover (λa, pathover B (b a) (q a) (b₂ a)) r p r₂ :=
  begin
    induction p, esimp at s, apply pathover_idp_of_eq, apply eq_of_vdeg_squareover, exact s
  end

end eq
