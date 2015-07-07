/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Squares in a type
-/
import types.eq
open eq equiv is_equiv

namespace eq

  variables {A B : Type} {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ a₁ a₂ a₃ a₄ : A}
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

  definition hrefl [unfold 4] (p : a = a') : square idp idp p p :=
  by induction p; exact ids

  definition vrefl [unfold 4] (p : a = a') : square p p idp idp :=
  by induction p; exact ids

  definition hrfl [unfold 4] {p : a = a'} : square idp idp p p :=
  !hrefl
  definition vrfl [unfold 4] {p : a = a'} : square p p idp idp :=
  !vrefl

  definition hdeg_square [unfold 6] {p q : a = a'} (r : p = q) : square idp idp p q :=
  by induction r;apply hrefl

  definition vdeg_square [unfold 6] {p q : a = a'} (r : p = q) : square p q idp idp :=
  by induction r;apply vrefl

  definition hconcat [unfold 16] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (s₃₁ : square p₃₀ p₃₂ p₂₁ p₄₁)
    : square (p₁₀ ⬝ p₃₀) (p₁₂ ⬝ p₃₂) p₀₁ p₄₁ :=
  by induction s₃₁; exact s₁₁

  definition vconcat [unfold 16] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (s₁₃ : square p₁₂ p₁₄ p₀₃ p₂₃)
    : square p₁₀ p₁₄ (p₀₁ ⬝ p₀₃) (p₂₁ ⬝ p₂₃) :=
  by induction s₁₃; exact s₁₁

  definition hinverse [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀⁻¹ p₁₂⁻¹ p₂₁ p₀₁ :=
  by induction s₁₁;exact ids

  definition vinverse [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₂ p₁₀ p₀₁⁻¹ p₂₁⁻¹ :=
  by induction s₁₁;exact ids

  definition eq_vconcat [unfold 11] {p : a₀₀ = a₂₀} (r : p = p₁₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) :
    square p p₁₂ p₀₁ p₂₁ :=
  by induction r; exact s₁₁

  definition vconcat_eq [unfold 11] {p : a₀₂ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₁₂ = p) :
    square p₁₀ p p₀₁ p₂₁ :=
  by induction r; exact s₁₁

  definition eq_hconcat [unfold 11] {p : a₀₀ = a₀₂} (r : p = p₀₁) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) :
    square p₁₀ p₁₂ p p₂₁ :=
  by induction r; exact s₁₁

  definition hconcat_eq [unfold 11] {p : a₂₀ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p) :
    square p₁₀ p₁₂ p₀₁ p :=
  by induction r; exact s₁₁


  infix `⬝h`:75 := hconcat
  infix `⬝v`:75 := vconcat
  infix `⬝hp`:75 := hconcat_eq
  infix `⬝vp`:75 := vconcat_eq
  infix `⬝ph`:75 := eq_hconcat
  infix `⬝pv`:75 := eq_vconcat
  postfix `⁻¹ʰ`:(max+1) := hinverse
  postfix `⁻¹ᵛ`:(max+1) := vinverse

  definition transpose [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₀₁ p₂₁ p₁₀ p₁₂ :=
  by induction s₁₁;exact ids

  definition aps {B : Type} (f : A → B) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square (ap f p₁₀) (ap f p₁₂) (ap f p₀₁) (ap f p₂₁) :=
  by induction s₁₁;exact ids

  definition natural_square [unfold 8] {f g : A → B} (p : f ~ g) (q : a = a') :
    square (ap f q) (ap g q) (p a) (p a') :=
  eq.rec_on q hrfl

  definition natural_square_tr [unfold 8] {f g : A → B} (p : f ~ g) (q : a = a') :
    square (p a) (p a') (ap f q) (ap g q) :=
  eq.rec_on q vrfl

  definition whisker_tl (p : a = a₀₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square (p ⬝ p₁₀) p₁₂ (p ⬝ p₀₁) p₂₁ :=
  by induction s₁₁;induction p;exact ids

  definition whisker_br (p : a₂₂ = a) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square p₁₀ (p₁₂ ⬝ p) p₀₁ (p₂₁ ⬝ p) :=
  by induction p;exact s₁₁

  /- some higher ∞-groupoid operations -/

  definition vconcat_vrfl (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : s₁₁ ⬝v vrefl p₁₂ = s₁₁ :=
  by induction s₁₁; reflexivity

  definition hconcat_hrfl (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : s₁₁ ⬝h hrefl p₂₁ = s₁₁ :=
  by induction s₁₁; reflexivity

  /- equivalences -/

  definition eq_of_square [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂ :=
  by induction s₁₁; apply idp

  definition square_of_eq (r : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂) : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p₁₂; esimp [concat] at r; induction r; induction p₂₁; induction p₁₀; exact ids

  definition eq_top_of_square [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : p₁₀ = p₀₁ ⬝ p₁₂ ⬝ p₂₁⁻¹ :=
  by induction s₁₁; apply idp

  definition square_of_eq_top (r : p₁₀ = p₀₁ ⬝ p₁₂ ⬝ p₂₁⁻¹) : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p₂₁; induction p₁₂; esimp at r;induction r;induction p₁₀;exact ids

  definition square_equiv_eq [constructor] (t : a₀₀ = a₀₂) (b : a₂₀ = a₂₂)
    (l : a₀₀ = a₂₀) (r : a₀₂ = a₂₂) : square t b l r ≃ t ⬝ r = l ⬝ b :=
  begin
    fapply equiv.MK,
    { exact eq_of_square},
    { exact square_of_eq},
    { intro s, induction b, esimp [concat] at s, induction s, induction r, induction t, apply idp},
    { intro s, induction s, apply idp},
  end

  definition hdeg_square_equiv' [constructor] (p q : a = a') : square idp idp p q ≃ p = q :=
  by transitivity _;apply square_equiv_eq;transitivity _;apply eq_equiv_eq_symm;
     apply equiv_eq_closed_right;apply idp_con

  definition vdeg_square_equiv' [constructor] (p q : a = a') : square p q idp idp ≃ p = q :=
  by transitivity _;apply square_equiv_eq;apply equiv_eq_closed_right; apply idp_con

  definition eq_of_hdeg_square [reducible] {p q : a = a'} (s : square idp idp p q) : p = q :=
  to_fun !hdeg_square_equiv' s

  definition eq_of_vdeg_square [reducible] {p q : a = a'} (s : square p q idp idp) : p = q :=
  to_fun !vdeg_square_equiv' s

  definition top_deg_square (l : a₁ = a₂) (b : a₂ = a₃) (r : a₄ = a₃) : square (l ⬝ b ⬝ r⁻¹) b l r :=
  by induction r;induction b;induction l;constructor

  /-
    the following two equivalences have as underlying inverse function the functions
    hdeg_square and vdeg_square, respectively.
    See examples below the definition
  -/
  definition hdeg_square_equiv [constructor] (p q : a = a') : square idp idp p q ≃ p = q :=
  begin
    fapply equiv_change_fun,
    { fapply equiv_change_inv, apply hdeg_square_equiv', exact hdeg_square,
        intro s, induction s, induction p, reflexivity},
    { exact eq_of_hdeg_square},
    { reflexivity}
  end

  definition vdeg_square_equiv [constructor] (p q : a = a') : square p q idp idp ≃ p = q :=
  begin
    fapply equiv_change_fun,
    { fapply equiv_change_inv, apply vdeg_square_equiv',exact vdeg_square,
        intro s, induction s, induction p, reflexivity},
    { exact eq_of_vdeg_square},
    { reflexivity}
  end

  -- example (p q : a = a') : to_inv (hdeg_square_equiv' p q) = hdeg_square := idp -- this fails
  example (p q : a = a') : to_inv (hdeg_square_equiv p q) = hdeg_square := idp

  definition pathover_eq [unfold 7] {f g : A → B} {p : a = a'} {q : f a = g a} {r : f a' = g a'}
    (s : square q r (ap f p) (ap g p)) : q =[p] r :=
  by induction p;apply pathover_idp_of_eq;exact eq_of_vdeg_square s

  definition square_of_pathover [unfold 7]
    {f g : A → B} {p : a = a'} {q : f a = g a} {r : f a' = g a'}
    (s : q =[p] r) : square q r (ap f p) (ap g p) :=
  by induction p;apply vdeg_square;exact eq_of_pathover_idp s

  /- interaction of equivalences with operations on squares -/

  definition pathover_eq_equiv_square [constructor] {f g : A → B}
    (p : a = a') (q : f a = g a) (r : f a' = g a') : q =[p] r ≃ square q r (ap f p) (ap g p) :=
  equiv.MK square_of_pathover
           pathover_eq
           begin
             intro s, induction p, esimp [square_of_pathover,pathover_eq],
             exact ap vdeg_square (to_right_inv !pathover_idp (eq_of_vdeg_square s))
               ⬝ to_left_inv !vdeg_square_equiv s
           end
           begin
             intro s, induction p, esimp [square_of_pathover,pathover_eq],
             exact ap pathover_idp_of_eq (to_right_inv !vdeg_square_equiv (eq_of_pathover_idp s))
               ⬝ to_left_inv !pathover_idp s
           end

  definition square_of_pathover_eq_concato {f g : A → B} {p : a = a'} {q q' : f a = g a}
    {r : f a' = g a'} (s' : q = q') (s : q' =[p] r)
    : square_of_pathover (s' ⬝po s) = s' ⬝pv square_of_pathover s :=
  by induction s;induction s';reflexivity

  definition square_of_pathover_concato_eq {f g : A → B} {p : a = a'} {q : f a = g a}
    {r r' : f a' = g a'} (s' : r = r') (s : q =[p] r)
    : square_of_pathover (s ⬝op s') = square_of_pathover s ⬝vp s' :=
  by induction s;induction s';reflexivity

  definition square_of_pathover_concato {f g : A → B} {p : a = a'} {p' : a' = a''} {q : f a = g a}
    {q' : f a' = g a'} {q'' : f a'' = g a''} (s : q =[p] q') (s' : q' =[p'] q'')
    : square_of_pathover (s ⬝o s')
  = ap_con f p p' ⬝ph (square_of_pathover s ⬝v square_of_pathover s') ⬝hp (ap_con g p p')⁻¹ :=
  by induction s';induction s;esimp [ap_con,hconcat_eq];exact !vconcat_vrfl⁻¹

  definition eq_of_square_hdeg_square {p q : a = a'} (r : p = q)
    : eq_of_square (hdeg_square r) = !idp_con ⬝ r⁻¹ :=
  by induction r;induction p;reflexivity

  definition eq_of_square_vdeg_square {p q : a = a'} (r : p = q)
    : eq_of_square (vdeg_square r) = r ⬝ !idp_con⁻¹ :=
  by induction r;induction p;reflexivity

  definition eq_of_square_eq_vconcat {p : a₀₀ = a₂₀} (r : p = p₁₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : eq_of_square (r ⬝pv s₁₁) = whisker_right r p₂₁ ⬝ eq_of_square s₁₁ :=
  by induction s₁₁;cases r;reflexivity

  definition eq_of_square_eq_hconcat {p : a₀₀ = a₀₂} (r : p = p₀₁) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : eq_of_square (r ⬝ph s₁₁) = eq_of_square s₁₁ ⬝ (whisker_right r p₁₂)⁻¹ :=
  by induction r;reflexivity

  definition eq_of_square_vconcat_eq {p : a₀₂ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₁₂ = p)
    : eq_of_square (s₁₁ ⬝vp r) = eq_of_square s₁₁ ⬝ whisker_left p₀₁ r :=
  by induction r;reflexivity

  definition eq_of_square_hconcat_eq {p : a₂₀ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p)
    : eq_of_square (s₁₁ ⬝hp r) = (whisker_left p₁₀ r)⁻¹ ⬝ eq_of_square s₁₁ :=
  by induction s₁₁; induction r;reflexivity


  -- definition vconcat_eq [unfold 11] {p : a₀₂ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₁₂ = p) :
  --   square p₁₀ p p₀₁ p₂₁ :=
  -- by induction r; exact s₁₁

  -- definition eq_hconcat [unfold 11] {p : a₀₀ = a₀₂} (r : p = p₀₁)
  --   (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀ p₁₂ p p₂₁ :=
  -- by induction r; exact s₁₁

  -- definition hconcat_eq [unfold 11] {p : a₂₀ = a₂₂}
  --   (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p) : square p₁₀ p₁₂ p₀₁ p :=
  -- by induction r; exact s₁₁


  -- the following definition is very slow, maybe it's interesting to see why?
  -- definition pathover_eq_equiv_square' {f g : A → B}(p : a = a') (q : f a = g a) (r : f a' = g a')
  --   : square q r (ap f p) (ap g p) ≃ q =[p] r :=
  -- equiv.MK pathover_eq
  --          square_of_pathover
  --          (λs, begin
  --                 induction p, rewrite [↑[square_of_pathover,pathover_eq],
  --                   to_right_inv !vdeg_square_equiv (eq_of_pathover_idp s),
  --                   to_left_inv !pathover_idp s]
  --               end)
  --          (λs, begin
  --                 induction p, rewrite [↑[square_of_pathover,pathover_eq],▸*,
  --                   to_right_inv !(@pathover_idp A) (eq_of_vdeg_square s),
  --                   to_left_inv !vdeg_square_equiv s]
  --               end)

  /- recursors for squares where some sides are reflexivity -/

  definition rec_on_b [recursor] {a₀₀ : A}
    {P : Π{a₂₀ a₁₂ : A} {t : a₀₀ = a₂₀} {l : a₀₀ = a₁₂} {r : a₂₀ = a₁₂}, square t idp l r → Type}
    {a₂₀ a₁₂ : A} {t : a₀₀ = a₂₀} {l : a₀₀ = a₁₂} {r : a₂₀ = a₁₂}
      (s : square t idp l r) (H : P ids) : P s :=
  have H2 : P (square_of_eq (eq_of_square s)),
    from eq.rec_on (eq_of_square s : t ⬝ r = l) (by induction r; induction t; exact H),
  left_inv (to_fun !square_equiv_eq) s ▸ H2

  definition rec_on_r [recursor] {a₀₀ : A}
    {P : Π{a₀₂ a₂₁ : A} {t : a₀₀ = a₂₁} {b : a₀₂ = a₂₁} {l : a₀₀ = a₀₂}, square t b l idp → Type}
    {a₀₂ a₂₁ : A} {t : a₀₀ = a₂₁} {b : a₀₂ = a₂₁} {l : a₀₀ = a₀₂}
      (s : square t b l idp) (H : P ids) : P s :=
  let p : l ⬝ b = t := (eq_of_square s)⁻¹ in
  have H2 : P (square_of_eq (eq_of_square s)⁻¹⁻¹),
    from @eq.rec_on _ _ (λx p, P (square_of_eq p⁻¹)) _ p (by induction b; induction l; exact H),
  left_inv (to_fun !square_equiv_eq) s ▸ !inv_inv ▸ H2

  definition rec_on_l [recursor] {a₀₁ : A}
    {P : Π {a₂₀ a₂₂ : A} {t : a₀₁ = a₂₀} {b : a₀₁ = a₂₂} {r : a₂₀ = a₂₂},
      square t b idp r → Type}
    {a₂₀ a₂₂ : A} {t : a₀₁ = a₂₀} {b : a₀₁ = a₂₂} {r : a₂₀ = a₂₂}
      (s : square t b idp r) (H : P ids) : P s :=
  let p : t ⬝ r = b := eq_of_square s ⬝ !idp_con in
  have H2 : P (square_of_eq (p ⬝ !idp_con⁻¹)),
    from eq.rec_on p (by induction r; induction t; exact H),
  left_inv (to_fun !square_equiv_eq) s ▸ !con_inv_cancel_right ▸ H2

  definition rec_on_t [recursor] {a₁₀ : A}
    {P : Π {a₀₂ a₂₂ : A} {b : a₀₂ = a₂₂} {l : a₁₀ = a₀₂} {r : a₁₀ = a₂₂}, square idp b l r → Type}
    {a₀₂ a₂₂ : A} {b : a₀₂ = a₂₂} {l : a₁₀ = a₀₂} {r : a₁₀ = a₂₂}
      (s : square idp b l r) (H : P ids) : P s :=
  let p : l ⬝ b = r := (eq_of_square s)⁻¹ ⬝ !idp_con in
  assert H2 : P (square_of_eq ((p ⬝ !idp_con⁻¹)⁻¹)),
    from eq.rec_on p (by induction b; induction l; exact H),
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
    from eq.rec_on (eq_of_square s : idp ⬝ r = l) (by induction r; exact H),
  left_inv (to_fun !square_equiv_eq) s ▸ H2

  definition rec_on_lr [recursor] {a : A}
    {P : Π{a' : A} {t : a = a'} {b : a = a'}, square t b idp idp → Type}
    {a' : A} {t : a = a'} {b : a = a'}
      (s : square t b idp idp) (H : P ids) : P s :=
  let p : idp ⬝ b = t := (eq_of_square s)⁻¹ in
  assert H2 : P (square_of_eq (eq_of_square s)⁻¹⁻¹),
    from @eq.rec_on _ _ (λx q, P (square_of_eq q⁻¹)) _ p (by induction b; exact H),
  to_left_inv (!square_equiv_eq) s ▸ !inv_inv ▸ H2

  --we can also do the other recursors (tl, tr, bl, br, tbl, tbr, tlr, blr), but let's postpone this until they are needed

  /- squares commute with some operations on 2-paths -/

  definition square_inv2 {p₁ p₂ p₃ p₄ : a = a'}
    {t : p₁ = p₂} {b : p₃ = p₄} {l : p₁ = p₃} {r : p₂ = p₄} (s : square t b l r)
    : square (inverse2 t) (inverse2 b) (inverse2 l) (inverse2 r) :=
  by induction s;constructor

  definition square_con2 {p₁ p₂ p₃ p₄ : a₁ = a₂} {q₁ q₂ q₃ q₄ : a₂ = a₃}
    {t₁ : p₁ = p₂} {b₁ : p₃ = p₄} {l₁ : p₁ = p₃} {r₁ : p₂ = p₄}
    {t₂ : q₁ = q₂} {b₂ : q₃ = q₄} {l₂ : q₁ = q₃} {r₂ : q₂ = q₄}
    (s₁ : square t₁ b₁ l₁ r₁) (s₂ : square t₂ b₂ l₂ r₂)
      : square (t₁ ◾ t₂) (b₁ ◾ b₂) (l₁ ◾ l₂) (r₁ ◾ r₂) :=
  by induction s₂;induction s₁;constructor

  -- definition square_of_con_inv_hsquare {p₁ p₂ p₃ p₄ : a₁ = a₂}
  --   {t : p₁ = p₂} {b : p₃ = p₄} {l : p₁ = p₃} {r : p₂ = p₄}
  --   (s : square (con_inv_eq_idp t) (con_inv_eq_idp b) (l ◾ r⁻²) idp)
  --     : square t b l r :=
  -- sorry --by induction s

end eq
