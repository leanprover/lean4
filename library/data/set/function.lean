/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Andrew Zipperer, Haitao Zhang

Functions between subsets of finite types.
-/
import .basic
open function eq.ops

namespace set

variables {X Y Z : Type}

abbreviation eq_on (f1 f2 : X → Y) (a : set X) : Prop :=
∀₀ x ∈ a, f1 x = f2 x

/- image -/

definition image (f : X → Y) (a : set X) : set Y := {y : Y | ∃x, x ∈ a ∧ f x = y}
notation f `'[`:max a `]` := image f a

theorem image_eq_image_of_eq_on {f1 f2 : X → Y} {a : set X} (H1 : eq_on f1 f2 a) :
  f1 '[a] = f2 '[a] :=
setext (take y, iff.intro
  (assume H2,
    obtain x (H3 : x ∈ a ∧ f1 x = y), from H2,
    have H4 : x ∈ a, from and.left H3,
    have H5 : f2 x = y, from (H1 H4)⁻¹ ⬝ and.right H3,
    exists.intro x (and.intro H4 H5))
  (assume H2,
    obtain x (H3 : x ∈ a ∧ f2 x = y), from H2,
    have H4 : x ∈ a, from and.left H3,
    have H5 : f1 x = y, from (H1 H4) ⬝ and.right H3,
    exists.intro x (and.intro H4 H5)))

theorem mem_image {f : X → Y} {a : set X} {x : X} {y : Y}
  (H1 : x ∈ a) (H2 : f x = y) : y ∈ f '[a] :=
exists.intro x (and.intro H1 H2)

theorem mem_image_of_mem (f : X → Y) {x : X} {a : set X} (H : x ∈ a) : f x ∈ image f a :=
mem_image H rfl

lemma image_compose (f : Y → Z) (g : X → Y) (a : set X) : (f ∘ g) '[a] = f '[g '[a]] :=
setext (take z,
  iff.intro
    (assume Hz : z ∈ (f ∘ g) '[a],
      obtain x (Hx₁ : x ∈ a) (Hx₂ : f (g x) = z), from Hz,
      have Hgx : g x ∈ g '[a], from mem_image Hx₁ rfl,
      show z ∈ f '[g '[a]], from mem_image Hgx Hx₂)
    (assume Hz : z ∈ f '[g '[a]],
      obtain y (Hy₁ : y ∈ g '[a]) (Hy₂ : f y = z), from Hz,
      obtain x (Hz₁ : x ∈ a) (Hz₂ : g x = y),      from Hy₁,
      show z ∈ (f ∘ g) '[a], from mem_image Hz₁ (Hz₂⁻¹ ▸ Hy₂)))

lemma image_subset {a b : set X} (f : X → Y) (H : a ⊆ b) : f '[a] ⊆ f '[b] :=
take y, assume Hy : y ∈ f '[a],
obtain x (Hx₁ : x ∈ a) (Hx₂ : f x = y), from Hy,
mem_image (H Hx₁) Hx₂

theorem image_union (f : X → Y) (s t : set X) :
  image f (s ∪ t) = image f s ∪ image f t :=
setext (take y, iff.intro
  (assume H : y ∈ image f (s ∪ t),
    obtain x [(xst : x ∈ s ∪ t) (fxy : f x = y)], from H,
    or.elim xst
      (assume xs, or.inl (mem_image xs fxy))
      (assume xt, or.inr (mem_image xt fxy)))
  (assume H : y ∈ image f s ∪ image f t,
    or.elim H
      (assume yifs : y ∈ image f s,
        obtain x [(xs : x ∈ s) (fxy : f x = y)], from yifs,
        mem_image (or.inl xs) fxy)
      (assume yift : y ∈ image f t,
        obtain x [(xt : x ∈ t) (fxy : f x = y)], from yift,
        mem_image (or.inr xt) fxy)))

/- maps to -/

definition maps_to [reducible] (f : X → Y) (a : set X) (b : set Y) : Prop := ∀⦃x⦄, x ∈ a → f x ∈ b

theorem maps_to_of_eq_on {f1 f2 : X → Y} {a : set X} {b : set Y} (eq_on_a : eq_on f1 f2 a)
    (maps_to_f1 : maps_to f1 a b) :
  maps_to f2 a b :=
take x,
assume xa : x ∈ a,
have H : f1 x ∈ b, from maps_to_f1 xa,
show f2 x ∈ b, from eq_on_a xa ▸ H

theorem maps_to_compose {g : Y → Z} {f : X → Y} {a : set X} {b : set Y} {c : set Z}
   (H1 : maps_to g b c) (H2 : maps_to f a b) : maps_to (g ∘ f) a c :=
take x, assume H : x ∈ a, H1 (H2 H)

theorem maps_to_univ_univ (f : X → Y) : maps_to f univ univ :=
take x, assume H, trivial

/- injectivity -/

definition inj_on [reducible] (f : X → Y) (a : set X) : Prop :=
∀⦃x1 x2 : X⦄, x1 ∈ a → x2 ∈ a → f x1 = f x2 → x1 = x2

theorem inj_on_empty (f : X → Y) : inj_on f ∅ :=
  take x₁ x₂, assume H₁ H₂ H₃, false.elim H₁

theorem inj_on_of_eq_on {f1 f2 : X → Y} {a : set X} (eq_f1_f2 : eq_on f1 f2 a)
    (inj_f1 : inj_on f1 a) :
  inj_on f2 a :=
take x1 x2 : X,
assume ax1 : x1 ∈ a,
assume ax2 : x2 ∈ a,
assume H : f2 x1 = f2 x2,
have H' : f1 x1 = f1 x2, from eq_f1_f2 ax1 ⬝ H ⬝ (eq_f1_f2 ax2)⁻¹,
show x1 = x2, from inj_f1 ax1 ax2 H'

theorem inj_on_compose {g : Y → Z} {f : X → Y} {a : set X} {b : set Y}
    (fab : maps_to f a b) (Hg : inj_on g b) (Hf: inj_on f a) :
  inj_on (g ∘ f) a :=
take x1 x2 : X,
assume x1a : x1 ∈ a,
assume x2a : x2 ∈ a,
have  fx1b : f x1 ∈ b, from fab x1a,
have  fx2b : f x2 ∈ b, from fab x2a,
assume  H1 : g (f x1) = g (f x2),
have    H2 : f x1 = f x2, from Hg fx1b fx2b H1,
show x1 = x2, from Hf x1a x2a H2

theorem inj_on_of_inj_on_of_subset {f : X → Y} {a b : set X} (H1 : inj_on f b) (H2 : a ⊆ b) :
  inj_on f a :=
take x1 x2 : X, assume (x1a : x1 ∈ a) (x2a : x2 ∈ a),
assume H : f x1 = f x2,
show x1 = x2, from H1 (H2 x1a) (H2 x2a) H

lemma injective_iff_inj_on_univ {f : X → Y} : injective f ↔ inj_on f univ :=
iff.intro
  (assume H, take x₁ x₂, assume ax₁ ax₂, H x₁ x₂)
  (assume H : inj_on f univ,
     take x₁ x₂ Heq,
     show x₁ = x₂, from H trivial trivial Heq)

/- surjectivity -/

definition surj_on [reducible] (f : X → Y) (a : set X) (b : set Y) : Prop := b ⊆ f '[a]

theorem surj_on_of_eq_on {f1 f2 : X → Y} {a : set X} {b : set Y} (eq_f1_f2 : eq_on f1 f2 a)
    (surj_f1 : surj_on f1 a b) :
  surj_on f2 a b :=
take y, assume H : y ∈ b,
obtain x (H1 : x ∈ a ∧ f1 x = y), from surj_f1 H,
have H2 : x ∈ a, from and.left H1,
have H3 : f2 x = y, from (eq_f1_f2 H2)⁻¹ ⬝ and.right H1,
exists.intro x (and.intro H2 H3)

theorem surj_on_compose {g : Y → Z} {f : X → Y} {a : set X} {b : set Y} {c : set Z}
  (Hg : surj_on g b c) (Hf: surj_on f a b) :
  surj_on (g ∘ f) a c :=
take z,
assume zc : z ∈ c,
obtain y (H1 : y ∈ b ∧ g y = z), from Hg zc,
obtain x (H2 : x ∈ a ∧ f x = y), from Hf (and.left H1),
show ∃x, x ∈ a ∧ g (f x) = z, from
  exists.intro x
    (and.intro
      (and.left H2)
      (calc
        g (f x) = g y : {and.right H2}
            ... = z   : and.right H1))

lemma surjective_iff_surj_on_univ {f : X → Y} : surjective f ↔ surj_on f univ univ :=
iff.intro
  (assume H, take y, assume Hy,
    obtain x Hx, from H y,
    mem_image trivial Hx)
  (assume H, take y,
    obtain x H1x H2x, from H y trivial,
    exists.intro x H2x)

/- bijectivity -/

definition bij_on [reducible] (f : X → Y) (a : set X) (b : set Y) : Prop :=
maps_to f a b ∧ inj_on f a ∧ surj_on f a b

theorem bij_on_of_eq_on {f1 f2 : X → Y} {a : set X} {b : set Y} (eqf : eq_on f1 f2 a)
     (H : bij_on f1 a b) : bij_on f2 a b :=
match H with and.intro Hmap (and.intro Hinj Hsurj) :=
  and.intro
    (maps_to_of_eq_on eqf Hmap)
    (and.intro
      (inj_on_of_eq_on eqf Hinj)
      (surj_on_of_eq_on eqf Hsurj))
end

theorem bij_on_compose {g : Y → Z} {f : X → Y} {a : set X} {b : set Y} {c : set Z}
  (Hg : bij_on g b c) (Hf: bij_on f a b) :
  bij_on (g ∘ f) a c :=
match Hg with and.intro Hgmap (and.intro Hginj Hgsurj) :=
  match Hf with and.intro Hfmap (and.intro Hfinj Hfsurj) :=
    and.intro
      (maps_to_compose Hgmap Hfmap)
      (and.intro
        (inj_on_compose Hfmap Hginj Hfinj)
        (surj_on_compose Hgsurj Hfsurj))
  end
end

lemma bijective_iff_bij_on_univ {f : X → Y} : bijective f ↔ bij_on f univ univ :=
iff.intro
  (assume H,
    obtain Hinj Hsurj, from H,
    and.intro (maps_to_univ_univ f)
      (and.intro
        (iff.mp !injective_iff_inj_on_univ Hinj)
        (iff.mp !surjective_iff_surj_on_univ Hsurj)))
 (assume H,
    obtain Hmaps Hinj Hsurj, from H,
      (and.intro
        (iff.mpr !injective_iff_inj_on_univ Hinj)
        (iff.mpr !surjective_iff_surj_on_univ Hsurj)))

/- left inverse -/

-- g is a left inverse to f on a
definition left_inv_on [reducible] (g : Y → X) (f : X → Y) (a : set X) : Prop :=
∀₀ x ∈ a, g (f x) = x

theorem left_inv_on_of_eq_on_left {g1 g2 : Y → X} {f : X → Y} {a : set X} {b : set Y}
  (fab : maps_to f a b) (eqg : eq_on g1 g2 b) (H : left_inv_on g1 f a) : left_inv_on g2 f a :=
take x,
assume xa : x ∈ a,
calc
  g2 (f x) = g1 (f x) : (eqg (fab xa))⁻¹
       ... = x        : H xa

theorem left_inv_on_of_eq_on_right {g : Y → X} {f1 f2 : X → Y} {a : set X}
  (eqf : eq_on f1 f2 a) (H : left_inv_on g f1 a) : left_inv_on g f2 a :=
take x,
assume xa : x ∈ a,
calc
  g (f2 x) = g (f1 x) : {(eqf xa)⁻¹}
       ... = x        : H xa

theorem inj_on_of_left_inv_on {g : Y → X} {f : X → Y} {a : set X} (H : left_inv_on g f a) :
  inj_on f a :=
take x1 x2,
assume x1a : x1 ∈ a,
assume x2a : x2 ∈ a,
assume H1 : f x1 = f x2,
calc
  x1     = g (f x1) : H x1a
     ... = g (f x2) : H1
     ... = x2       : H x2a

theorem left_inv_on_compose {f' : Y → X} {g' : Z → Y} {g : Y → Z} {f : X → Y}
   {a : set X} {b : set Y} (fab : maps_to f a b)
    (Hf : left_inv_on f' f a) (Hg : left_inv_on g' g b) : left_inv_on (f' ∘ g') (g ∘ f) a :=
take x : X,
assume xa : x ∈ a,
have fxb : f x ∈ b, from fab xa,
calc
  f' (g' (g (f x))) = f' (f x) : Hg fxb
                ... = x        : Hf xa

/- right inverse -/

-- g is a right inverse to f on a
definition right_inv_on [reducible] (g : Y → X) (f : X → Y) (b : set Y) : Prop :=
left_inv_on f g b

theorem right_inv_on_of_eq_on_left {g1 g2 : Y → X} {f : X → Y} {a : set X} {b : set Y}
  (eqg : eq_on g1 g2 b) (H : right_inv_on g1 f b) : right_inv_on g2 f b :=
left_inv_on_of_eq_on_right eqg H

theorem right_inv_on_of_eq_on_right {g : Y → X} {f1 f2 : X → Y} {a : set X} {b : set Y}
  (gba : maps_to g b a) (eqf : eq_on f1 f2 a) (H : right_inv_on g f1 b) : right_inv_on g f2 b :=
left_inv_on_of_eq_on_left gba eqf H

theorem surj_on_of_right_inv_on {g : Y → X} {f : X → Y} {a : set X} {b : set Y}
    (gba : maps_to g b a) (H : right_inv_on g f b) :
  surj_on f a b :=
take y,
assume yb : y ∈ b,
have gya : g y ∈ a, from gba yb,
have H1 : f (g y) = y, from H yb,
exists.intro (g y) (and.intro gya H1)

theorem right_inv_on_compose {f' : Y → X} {g' : Z → Y} {g : Y → Z} {f : X → Y}
   {c : set Z} {b : set Y} (g'cb : maps_to g' c b)
    (Hf : right_inv_on f' f b) (Hg : right_inv_on g' g c) : right_inv_on (f' ∘ g') (g ∘ f) c :=
left_inv_on_compose g'cb Hg Hf

theorem right_inv_on_of_inj_on_of_left_inv_on {f : X → Y} {g : Y → X} {a : set X} {b : set Y}
    (fab : maps_to f a b) (gba : maps_to g b a) (injf : inj_on f a) (lfg : left_inv_on f g b) :
  right_inv_on f g a :=
take x, assume xa : x ∈ a,
have H : f (g (f x)) = f x, from lfg (fab xa),
injf (gba (fab xa)) xa H

theorem eq_on_of_left_inv_of_right_inv {g1 g2 : Y → X} {f : X → Y} {a : set X} {b : set Y}
  (g2ba : maps_to g2 b a) (Hg1 : left_inv_on g1 f a) (Hg2 : right_inv_on g2 f b) : eq_on g1 g2 b :=
take y,
assume yb : y ∈ b,
calc
  g1 y = g1 (f (g2 y)) : {(Hg2 yb)⁻¹}
   ... = g2 y          : Hg1 (g2ba yb)

theorem left_inv_on_of_surj_on_right_inv_on {f : X → Y} {g : Y → X} {a : set X} {b : set Y}
    (surjf : surj_on f a b) (rfg : right_inv_on f g a) :
  left_inv_on f g b :=
take y, assume yb : y ∈ b,
obtain x (xa : x ∈ a) (Hx : f x = y), from surjf yb,
calc
  f (g y) = f (g (f x)) : Hx
      ... = f x         : rfg xa
      ... = y           : Hx

/- inverses -/

-- g is an inverse to f viewed as a map from a to b
definition inv_on [reducible] (g : Y → X) (f : X → Y) (a : set X) (b : set Y) : Prop :=
left_inv_on g f a ∧ right_inv_on g f b

theorem bij_on_of_inv_on {g : Y → X} {f : X → Y} {a : set X} {b : set Y} (fab : maps_to f a b)
  (gba : maps_to g b a) (H : inv_on g f a b) : bij_on f a b :=
and.intro fab
  (and.intro
    (inj_on_of_left_inv_on (and.left H))
    (surj_on_of_right_inv_on gba (and.right H)))

end set
