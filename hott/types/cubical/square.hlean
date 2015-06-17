/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Squares in a type
-/
import types.eq
open eq equiv is_equiv

namespace eq

  variables {A B : Type} {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ : A}
            /-a₀₀-/ {p₁₀ : a₀₀ = a₂₀} /-a₂₀-/ {p₃₀ : a₂₀ = a₄₀} /-a₄₀-/
       {p₀₁ : a₀₀ = a₀₂} /-s₁₁-/ {p₂₁ : a₂₀ = a₂₂} /-s₃₁-/ {p₄₁ : a₄₀ = a₄₂}
            /-a₀₂-/ {p₁₂ : a₀₂ = a₂₂} /-a₂₂-/ {p₃₂ : a₂₂ = a₄₂} /-a₄₂-/
       {p₀₃ : a₀₂ = a₀₄} /-s₁₃-/ {p₂₃ : a₂₂ = a₂₄} /-s₃₃-/ {p₄₃ : a₄₂ = a₄₄}
            /-a₀₄-/ {p₁₄ : a₀₄ = a₂₄} /-a₂₄-/ {p₃₄ : a₂₄ = a₄₄} /-a₄₄-/


  inductive square {A : Type} {a₀₀ : A}
    : Π{a₂₀ a₀₂ a₂₂ : A}, a₀₀ = a₂₀ → a₀₂ = a₂₂ → a₀₀ = a₀₂ → a₂₀ = a₂₂ → Type :=
  ids : square idp idp idp idp
  /- square top bottom left right -/

  variables {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁} {s₃₁ : square p₃₀ p₃₂ p₂₁ p₄₁}
            {s₁₃ : square p₁₂ p₁₄ p₀₃ p₂₃} {s₃₃ : square p₃₂ p₃₄ p₂₃ p₄₃}

  definition ids      [reducible] [constructor]         := @square.ids
  definition idsquare [reducible] [constructor] (a : A) := @square.ids A a

  definition hrefl [unfold-c 4] (p : a = a') : square idp idp p p :=
  by cases p; exact ids

  definition vrefl [unfold-c 4] (p : a = a') : square p p idp idp :=
  by cases p; exact ids

  definition hrfl [unfold-c 4] {p : a = a'} : square idp idp p p :=
  !hrefl
  definition vrfl [unfold-c 4] {p : a = a'} : square p p idp idp :=
  !vrefl

  definition hconcat (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (s₃₁ : square p₃₀ p₃₂ p₂₁ p₄₁)
    : square (p₁₀ ⬝ p₃₀) (p₁₂ ⬝ p₃₂) p₀₁ p₄₁ :=
  by cases s₃₁; exact s₁₁

  definition vconcat (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (s₁₃ : square p₁₂ p₁₄ p₀₃ p₂₃)
    : square p₁₀ p₁₄ (p₀₁ ⬝ p₀₃) (p₂₁ ⬝ p₂₃) :=
  by cases s₁₃; exact s₁₁

  definition hinverse (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀⁻¹ p₁₂⁻¹ p₂₁ p₀₁ :=
  by cases s₁₁;exact ids

  definition vinverse (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₂ p₁₀ p₀₁⁻¹ p₂₁⁻¹ :=
  by cases s₁₁;exact ids

  definition transpose (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₀₁ p₂₁ p₁₀ p₁₂ :=
  by cases s₁₁;exact ids

  definition eq_of_square (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂ :=
  by cases s₁₁; apply idp

  definition square_of_eq (r : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂) : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by cases p₁₂; esimp [concat] at r; cases r; cases p₂₁; cases p₁₀; exact ids

  definition aps {B : Type} (f : A → B) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square (ap f p₁₀) (ap f p₁₂) (ap f p₀₁) (ap f p₂₁) :=
  by cases s₁₁;exact ids

  definition square_of_homotopy {B : Type} {f g : A → B} (H : f ~ g) (p : a = a')
    : square (H a) (H a') (ap f p) (ap g p) :=
  by cases p; apply vrefl

  definition square_of_homotopy' {B : Type} {f g : A → B} (H : f ~ g) (p : a = a')
    : square (ap f p) (ap g p) (H a) (H a') :=
  by cases p; apply hrefl

  definition square_equiv_eq (t : a₀₀ = a₀₂) (b : a₂₀ = a₂₂) (l : a₀₀ = a₂₀) (r : a₀₂ = a₂₂)
    : square t b l r ≃ t ⬝ r = l ⬝ b :=
  begin
    fapply equiv.MK,
    { exact eq_of_square},
    { exact square_of_eq},
    { intro s, cases b, esimp [concat] at s, cases s, cases r, cases t, apply idp},
    { intro s, cases s, apply idp},
  end

  definition hdeg_square {p q : a = a'} (r : p = q) : square idp idp p q :=
  by cases r;apply hrefl

  definition vdeg_square {p q : a = a'} (r : p = q) : square p q idp idp :=
  by cases r;apply vrefl

  definition hdeg_square_equiv' [constructor] (p q : a = a') : square idp idp p q ≃ p = q :=
  by transitivity _;apply square_equiv_eq;transitivity _;apply eq_equiv_eq_symm;
     apply equiv_eq_closed_right;apply idp_con

  definition vdeg_square_equiv' [constructor] (p q : a = a') : square p q idp idp ≃ p = q :=
  by transitivity _;apply square_equiv_eq;apply equiv_eq_closed_right; apply idp_con

  definition eq_of_hdeg_square [reducible] {p q : a = a'} (s : square idp idp p q) : p = q :=
  to_fun !hdeg_square_equiv' s

  definition eq_of_vdeg_square [reducible] {p q : a = a'} (s : square p q idp idp) : p = q :=
  to_fun !vdeg_square_equiv' s

  /-
    the following two equivalences have as underlying inverse function the functions
    hdeg_square and vdeg_square, respectively
  -/
  definition hdeg_square_equiv [constructor] (p q : a = a') : square idp idp p q ≃ p = q :=
  begin
    fapply equiv_change_fun,
    { fapply equiv_change_inv, apply hdeg_square_equiv', exact hdeg_square,
        intro s, cases s, cases p, reflexivity},
    { exact eq_of_hdeg_square},
    { reflexivity}
  end

  definition vdeg_square_equiv [constructor] (p q : a = a') : square p q idp idp ≃ p = q :=
  begin
    fapply equiv_change_fun,
    { fapply equiv_change_inv, apply vdeg_square_equiv',exact vdeg_square,
        intro s, cases s, cases p, reflexivity},
    { exact eq_of_vdeg_square},
    { reflexivity}
  end

  -- example (p q : a = a') : to_inv (hdeg_square_equiv' p q) = hdeg_square := idp -- this fails
  example (p q : a = a') : to_inv (hdeg_square_equiv p q) = hdeg_square := idp

  definition natural_square [unfold-c 8] {f g : A → B} (p : f ~ g) (q : a = a') :
    square (p a) (p a') (ap f q) (ap g q) :=
  eq.rec_on q vrfl

  definition rec_on_b [recursor] {a₀₀ : A}
    {P : Π{a₂₀ a₁₂ : A} {t : a₀₀ = a₂₀} {l : a₀₀ = a₁₂} {r : a₂₀ = a₁₂}, square t idp l r → Type}
    {a₂₀ a₁₂ : A} {t : a₀₀ = a₂₀} {l : a₀₀ = a₁₂} {r : a₂₀ = a₁₂}
      (s : square t idp l r) (H : P ids) : P s :=
  have H2 : P (square_of_eq (eq_of_square s)),
    from eq.rec_on (eq_of_square s : t ⬝ r = l) (by cases r; cases t; exact H),
  left_inv (to_fun !square_equiv_eq) s ▸ H2

  definition rec_on_r [recursor] {a₀₀ : A}
    {P : Π{a₀₂ a₂₁ : A} {t : a₀₀ = a₂₁} {b : a₀₂ = a₂₁} {l : a₀₀ = a₀₂}, square t b l idp → Type}
    {a₀₂ a₂₁ : A} {t : a₀₀ = a₂₁} {b : a₀₂ = a₂₁} {l : a₀₀ = a₀₂}
      (s : square t b l idp) (H : P ids) : P s :=
  let p : l ⬝ b = t := (eq_of_square s)⁻¹ in
  have H2 : P (square_of_eq (eq_of_square s)⁻¹⁻¹),
    from @eq.rec_on _ _ (λx p, P (square_of_eq p⁻¹)) _ p (by cases b; cases l; exact H),
  left_inv (to_fun !square_equiv_eq) s ▸ !inv_inv ▸ H2

  definition rec_on_l [recursor] {a₀₁ : A}
    {P : Π {a₂₀ a₂₂ : A} {t : a₀₁ = a₂₀} {b : a₀₁ = a₂₂} {r : a₂₀ = a₂₂},
      square t b idp r → Type}
    {a₂₀ a₂₂ : A} {t : a₀₁ = a₂₀} {b : a₀₁ = a₂₂} {r : a₂₀ = a₂₂}
      (s : square t b idp r) (H : P ids) : P s :=
  let p : t ⬝ r = b := eq_of_square s ⬝ !idp_con in
  have H2 : P (square_of_eq (p ⬝ !idp_con⁻¹)),
    from eq.rec_on p (by cases r; cases t; exact H),
  left_inv (to_fun !square_equiv_eq) s ▸ !con_inv_cancel_right ▸ H2

  definition rec_on_t [recursor] {a₁₀ : A}
    {P : Π {a₀₂ a₂₂ : A} {b : a₀₂ = a₂₂} {l : a₁₀ = a₀₂} {r : a₁₀ = a₂₂}, square idp b l r → Type}
    {a₀₂ a₂₂ : A} {b : a₀₂ = a₂₂} {l : a₁₀ = a₀₂} {r : a₁₀ = a₂₂}
      (s : square idp b l r) (H : P ids) : P s :=
  let p : l ⬝ b = r := (eq_of_square s)⁻¹ ⬝ !idp_con in
  assert H2 : P (square_of_eq ((p ⬝ !idp_con⁻¹)⁻¹)),
    from eq.rec_on p (by cases b; cases l; exact H),
  assert H3 : P (square_of_eq ((eq_of_square s)⁻¹⁻¹)),
    from eq.rec_on !con_inv_cancel_right H2,
  assert H4 : P (square_of_eq (eq_of_square s)),
    from eq.rec_on !inv_inv H3,
  proof
    left_inv (to_fun !square_equiv_eq) s ▸ H4
  qed

  definition rec_on_tb [recursor] {a : A}
    {P : Π{b : A} {l : a = b} {r : a = b}, square idp idp l r → Type}
    {b : A} {l : a = b} {r : a = b}
      (s : square idp idp l r) (H : P ids) : P s :=
  have H2 : P (square_of_eq (eq_of_square s)),
    from eq.rec_on (eq_of_square s : idp ⬝ r = l) (by cases r; exact H),
  left_inv (to_fun !square_equiv_eq) s ▸ H2

  definition rec_on_lr [recursor] {a : A}
    {P : Π{a' : A} {t : a = a'} {b : a = a'}, square t b idp idp → Type}
    {a' : A} {t : a = a'} {b : a = a'}
      (s : square t b idp idp) (H : P ids) : P s :=
  let p : idp ⬝ b = t := (eq_of_square s)⁻¹ in
  assert H2 : P (square_of_eq (eq_of_square s)⁻¹⁻¹),
    from @eq.rec_on _ _ (λx q, P (square_of_eq q⁻¹)) _ p (by cases b; exact H),
  to_left_inv (!square_equiv_eq) s ▸ !inv_inv ▸ H2

  --we can also do the other recursors (tl, tr, bl, br, tbl, tbr, tlr, blr), but let's postpone this until they are needed

  definition pathover_eq {f g : A → B} {p : a = a'} {q : f a = g a} {r : f a' = g a'}
    (s : square q r (ap f p) (ap g p)) : q =[p] r :=
  by cases p;apply pathover_idp_of_eq;exact eq_of_vdeg_square s

  definition square_of_pathover {f g : A → B} {p : a = a'} {q : f a = g a} {r : f a' = g a'}
    (s : q =[p] r) : square q r (ap f p) (ap g p) :=
  by cases p;apply vdeg_square;exact eq_of_pathover_idp s
exit
  definition pathover_eq_equiv_square {f g : A → B} (p : a = a') (q : f a = g a) (r : f a' = g a')
    : square q r (ap f p) (ap g p) ≃ q =[p] r :=
  equiv.MK pathover_eq
           square_of_pathover
           (λs, begin cases p, esimp [square_of_pathover,pathover_eq],
                let H := to_right_inv !vdeg_square_equiv (eq_of_pathover_idp s),
                esimp at H,
                rewrite [H] end
                   )
           (λs, by cases p;esimp [square_of_pathover,pathover_eq] at *)


  -- set_option pp.notation false
  -- set_option pp.implicit true
example {f g : A → B} (q : f a = g a) (r : f a = g a) (s : q =[idp] r) :
  function.compose (to_fun (vdeg_square_equiv q r)) (to_fun (vdeg_square_equiv q r))⁻¹
    (eq_of_pathover_idp s) = sorry :=
    begin
      esimp
    end

example {f g : A → B} (q : f a = g a) (r : f a = g a) (s : square q r idp idp) :
  to_fun (vdeg_square_equiv q r) s = eq_of_vdeg_square s :=
    begin

    end

end eq
