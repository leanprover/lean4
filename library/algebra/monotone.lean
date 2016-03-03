/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Weak and strict order preserving maps.

TODO: we will probably eventually want versions restricted to smaller domains,
"nondecreasing_on" etc. Maybe we can do this with subtypes.
-/
import .order
open eq eq.ops function

variables {A B C : Type}

section
  variables [weak_order A] [weak_order B] [weak_order C]

  definition nondecreasing (f : A → B) : Prop := ∀ ⦃a₁ a₂⦄, a₁ ≤ a₂ → f a₁ ≤ f a₂

  definition nonincreasing (f : A → B) : Prop := ∀ ⦃a₁ a₂⦄, a₁ ≤ a₂ → f a₁ ≥ f a₂

  theorem nondecreasing_id : nondecreasing (@id A) := take a₁ a₂, assume H, H

  theorem nondecreasing_comp_nondec_nondec {g : B → C} {f : A → B}
      (Hg : nondecreasing g) (Hf : nondecreasing f) : nondecreasing (g ∘ f) :=
  take a₁ a₂, assume H, Hg (Hf H)

  theorem nondecreasing_comp_noninc_noninc {g : B → C} {f : A → B}
      (Hg : nonincreasing g) (Hf : nonincreasing f) : nondecreasing (g ∘ f) :=
  take a₁ a₂, assume H, Hg (Hf H)

  theorem nonincreasing_comp_noninc_nondec {g : B → C} {f : A → B}
      (Hg : nonincreasing g) (Hf : nondecreasing f) : nonincreasing (g ∘ f) :=
  take a₁ a₂, assume H, Hg (Hf H)

  theorem nonincreasing_comp_nondec_noninc {g : B → C} {f : A → B}
      (Hg : nondecreasing g) (Hf : nonincreasing f) : nonincreasing (g ∘ f) :=
  take a₁ a₂, assume H, Hg (Hf H)
end

section
  variables [strict_order A] [strict_order B] [strict_order C]

  definition strictly_increasing (f : A → B) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ < a₂ → f a₁ < f a₂

  definition strictly_decreasing (f : A → B) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ < a₂ → f a₁ > f a₂

  theorem strictly_increasing_id : strictly_increasing (@id A) := take a₁ a₂, assume H, H

  theorem strictly_increasing_comp_inc_inc {g : B → C} {f : A → B}
      (Hg : strictly_increasing g) (Hf : strictly_increasing f) : strictly_increasing (g ∘ f) :=
  take a₁ a₂, assume H, Hg (Hf H)

  theorem strictly_increasing_comp_dec_dec {g : B → C} {f : A → B}
      (Hg : strictly_decreasing g) (Hf : strictly_decreasing f) : strictly_increasing (g ∘ f) :=
  take a₁ a₂, assume H, Hg (Hf H)

  theorem strictly_decreasing_comp_inc_dec {g : B → C} {f : A → B}
      (Hg : strictly_increasing g) (Hf : strictly_decreasing f) : strictly_decreasing (g ∘ f) :=
  take a₁ a₂, assume H, Hg (Hf H)

  theorem strictly_decreasing_comp_dec_inc {g : B → C} {f : A → B}
      (Hg : strictly_decreasing g) (Hf : strictly_increasing f) : strictly_decreasing (g ∘ f) :=
  take a₁ a₂, assume H, Hg (Hf H)
end

section
  variables [strong_order_pair A] [strong_order_pair B]

  theorem nondecreasing_of_strictly_increasing {f : A → B} (H : strictly_increasing f) :
    nondecreasing f :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  show f a₁ ≤ f a₂, from or.elim (lt_or_eq_of_le this)
    (suppose a₁ < a₂, le_of_lt (H this))
    (suppose a₁ = a₂, le_of_eq (congr_arg f this))

  theorem nonincreasing_of_strictly_decreasing {f : A → B} (H : strictly_decreasing f) :
    nonincreasing f :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  show f a₁ ≥ f a₂, from or.elim (lt_or_eq_of_le this)
    (suppose a₁ < a₂, le_of_lt (H this))
    (suppose a₁ = a₂, le_of_eq (congr_arg f this⁻¹))
end

section
  variables [linear_strong_order_pair A] [linear_strong_order_pair B] [linear_strong_order_pair C]

  theorem lt_of_strictly_increasing {f : A → B} {a₁ a₂ : A} (H : strictly_increasing f)
    (H' : f a₁ < f a₂) : a₁ < a₂ :=
  lt_of_not_ge (suppose a₂ ≤ a₁,
    have f a₂ ≤ f a₁, from nondecreasing_of_strictly_increasing H this,
    show false, from not_le_of_gt H' this)

  theorem lt_iff_of_strictly_increasing {f : A → B} (a₁ a₂ : A) (H : strictly_increasing f) :
    f a₁ < f a₂ ↔ a₁ < a₂ :=
  iff.intro (lt_of_strictly_increasing H) (@H a₁ a₂)

  theorem le_of_strictly_increasing {f : A → B} {a₁ a₂ : A} (H : strictly_increasing f)
    (H' : f a₁ ≤ f a₂) : a₁ ≤ a₂ :=
  le_of_not_gt (suppose a₂ < a₁, not_le_of_gt (H this) H')

  theorem le_iff_of_strictly_increasing {f : A → B} (a₁ a₂ : A) (H : strictly_increasing f) :
    f a₁ ≤ f a₂ ↔ a₁ ≤ a₂ :=
  iff.intro (le_of_strictly_increasing H) (λ H', nondecreasing_of_strictly_increasing H H')

  theorem lt_of_strictly_decreasing {f : A → B} {a₁ a₂ : A} (H : strictly_decreasing f)
    (H' : f a₁ > f a₂) : a₁ < a₂ :=
  lt_of_not_ge (suppose a₂ ≤ a₁,
    have f a₂ ≥ f a₁, from nonincreasing_of_strictly_decreasing H this,
    show false, from not_le_of_gt H' this)

  theorem gt_iff_of_strictly_decreasing {f : A → B} (a₁ a₂ : A) (H : strictly_decreasing f) :
    f a₁ > f a₂ ↔ a₁ < a₂ :=
  iff.intro (lt_of_strictly_decreasing H) (@H a₁ a₂)

  theorem le_of_strictly_decreasing {f : A → B} {a₁ a₂ : A} (H : strictly_decreasing f)
    (H' : f a₁ ≥ f a₂) : a₁ ≤ a₂ :=
  le_of_not_gt (suppose a₂ < a₁, not_le_of_gt (H this) H')

  theorem ge_iff_of_strictly_decreasing {f : A → B} (a₁ a₂ : A) (H : strictly_decreasing f) :
    f a₁ ≥ f a₂ ↔ a₁ ≤ a₂ :=
  iff.intro (le_of_strictly_decreasing H) (λ H', nonincreasing_of_strictly_decreasing H H')

  theorem strictly_increasing_of_left_inverse {g : B → A} {f : A → B} (H : left_inverse g f)
      (H' : strictly_increasing g) : strictly_increasing f :=
  take a₁ a₂, suppose a₁ < a₂,
  have g (f a₁) < g (f a₂), by rewrite *H; apply this,
  lt_of_strictly_increasing H' this

  theorem strictly_decreasing_of_left_inverse {g : B → A} {f : A → B} (H : left_inverse g f)
      (H' : strictly_decreasing g) : strictly_decreasing f :=
  take b₁ b₂, suppose b₁ < b₂,
  have g (f b₁) < g (f b₂), by rewrite *H; apply this,
  lt_of_strictly_decreasing H' this

  theorem nondecreasing_of_left_inverse {g : B → A} {f : A → B} (H : left_inverse g f)
      (H' : strictly_increasing g) : nondecreasing f :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  have g (f a₁) ≤ g (f a₂), by rewrite *H; apply this,
  le_of_strictly_increasing H' this

  theorem nonincreasing_of_left_inverse {g : B → A} {f : A → B} (H : left_inverse g f)
      (H' : strictly_decreasing g) : nonincreasing f :=
  take b₁ b₂, suppose b₁ ≤ b₂,
  have g (f b₁) ≤ g (f b₂), by rewrite *H; apply this,
  le_of_strictly_decreasing H' this
end

/- composition rules for strict orders -/

section
  variables [strict_order A] [strict_order B] [strict_order C]

  theorem strictly_increasing_of_strictly_increasing_comp_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_increasing h) (H₃ : strictly_increasing (g ∘ f)) :
    strictly_increasing f :=
  take a₁ a₂, suppose a₁ < a₂,
  have h (g (f a₁)) < h (g (f a₂)), from H₂ (H₃ this),
  show f a₁ < f a₂, by rewrite *H₁ at this; apply this

  theorem strictly_decreasing_of_strictly_increasing_comp_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_decreasing h) (H₃ : strictly_increasing (g ∘ f)) :
    strictly_decreasing f :=
  take a₁ a₂, suppose a₁ < a₂,
  have h (g (f a₁)) > h (g (f a₂)), from H₂ (H₃ this),
  show f a₁ > f a₂, by rewrite *H₁ at this; apply this

  theorem strictly_decreasing_of_strictly_decreasing_comp_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_increasing h) (H₃ : strictly_decreasing (g ∘ f)) :
    strictly_decreasing f :=
  take a₁ a₂, suppose a₁ < a₂,
  have h (g (f a₁)) > h (g (f a₂)), from H₂ (H₃ this),
  show f a₁ > f a₂, by rewrite *H₁ at this; apply this

  theorem strictly_increasing_of_strictly_decreasing_comp_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_decreasing h) (H₃ : strictly_decreasing (g ∘ f)) :
    strictly_increasing f :=
  take a₁ a₂, suppose a₁ < a₂,
  have h (g (f a₁)) < h (g (f a₂)), from H₂ (H₃ this),
  show f a₁ < f a₂, by rewrite *H₁ at this; apply this

  theorem strictly_increasing_of_strictly_decreasing_comp_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_decreasing h) (H₃ : strictly_decreasing (g ∘ f)) :
    strictly_increasing g :=
  take a₁ a₂, suppose a₁ < a₂,
  have g (f (h a₁)) < g (f (h a₂)), from H₃ (H₂ this),
  show g a₁ < g a₂, by rewrite *H₁ at this; apply this

  theorem strictly_decreasing_of_strictly_decreasing_comp_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_increasing h) (H₃ : strictly_decreasing (g ∘ f)) :
    strictly_decreasing g :=
  take a₁ a₂, suppose a₁ < a₂,
  have g (f (h a₁)) > g (f (h a₂)), from H₃ (H₂ this),
  show g a₁ > g a₂, by rewrite *H₁ at this; apply this

  theorem strictly_increasing_of_strictly_increasing_comp_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_increasing h) (H₃ : strictly_increasing (g ∘ f)) :
    strictly_increasing g :=
  take a₁ a₂, suppose a₁ < a₂,
  have g (f (h a₁)) < g (f (h a₂)), from H₃ (H₂ this),
  show g a₁ < g a₂, by rewrite *H₁ at this; apply this

  theorem strictly_decreasing_of_strictly_increasing_comp_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_decreasing h) (H₃ : strictly_increasing (g ∘ f)) :
    strictly_decreasing g :=
  take a₁ a₂, suppose a₁ < a₂,
  have g (f (h a₁)) > g (f (h a₂)), from H₃ (H₂ this),
  show g a₁ > g a₂, by rewrite *H₁ at this; apply this
end

section
  variables [strict_order A] [linear_strong_order_pair B] [linear_strong_order_pair C]

  theorem strictly_increasing_comp_iff_strictly_increasing_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_increasing h) :
    strictly_increasing (g ∘ f) ↔ strictly_increasing f :=
  have H₃ : strictly_increasing g, from strictly_increasing_of_left_inverse H₁ H₂,
  iff.intro
    (strictly_increasing_of_strictly_increasing_comp_right H₁ H₂)
    (strictly_increasing_comp_inc_inc H₃)

  theorem strictly_increasing_comp_iff_strictly_decreasing_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_decreasing h) :
    strictly_increasing (g ∘ f) ↔ strictly_decreasing f :=
  have H₃ : strictly_decreasing g, from strictly_decreasing_of_left_inverse H₁ H₂,
  iff.intro
    (strictly_decreasing_of_strictly_increasing_comp_right H₁ H₂)
    (strictly_increasing_comp_dec_dec H₃)

  theorem strictly_decreasing_comp_iff_strictly_decreasing_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_increasing h) :
    strictly_decreasing (g ∘ f) ↔ strictly_decreasing f :=
  have H₃ : strictly_increasing g, from strictly_increasing_of_left_inverse H₁ H₂,
  iff.intro
    (strictly_decreasing_of_strictly_decreasing_comp_right H₁ H₂)
    (strictly_decreasing_comp_inc_dec H₃)

  theorem strictly_decreasing_comp_iff_strictly_increasing_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_decreasing h) :
    strictly_decreasing (g ∘ f) ↔ strictly_increasing f :=
  have H₃ : strictly_decreasing g, from strictly_decreasing_of_left_inverse H₁ H₂,
  iff.intro
    (strictly_increasing_of_strictly_decreasing_comp_right H₁ H₂)
    (strictly_decreasing_comp_dec_inc H₃)
end

section
  variables [linear_strong_order_pair A] [linear_strong_order_pair B] [strict_order C]

  theorem strictly_increasing_comp_iff_strinctly_increasing_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_increasing f) :
    strictly_increasing (g ∘ f) ↔ strictly_increasing g :=
  have H₃ : strictly_increasing h, from strictly_increasing_of_left_inverse H₁ H₂,
  iff.intro
    (strictly_increasing_of_strictly_increasing_comp_left H₁ H₃)
    (λ H, strictly_increasing_comp_inc_inc H H₂)

  theorem strictly_increasing_comp_iff_strictly_decreasing_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_decreasing f) :
    strictly_increasing (g ∘ f) ↔ strictly_decreasing g :=
  have H₃ : strictly_decreasing h, from strictly_decreasing_of_left_inverse H₁ H₂,
  iff.intro
    (strictly_decreasing_of_strictly_increasing_comp_left H₁ H₃)
    (λ H, strictly_increasing_comp_dec_dec H H₂)

  theorem strictly_decreasing_comp_iff_strictly_increasing_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_decreasing f) :
    strictly_decreasing (g ∘ f) ↔ strictly_increasing g :=
  have H₃ : strictly_decreasing h, from strictly_decreasing_of_left_inverse H₁ H₂,
  iff.intro
    (strictly_increasing_of_strictly_decreasing_comp_left H₁ H₃)
    (λ H, strictly_decreasing_comp_inc_dec H H₂)

  theorem strictly_decreasing_comp_iff_strictly_decreasing_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_increasing f) :
    strictly_decreasing (g ∘ f) ↔ strictly_decreasing g :=
  have H₃ : strictly_increasing h, from strictly_increasing_of_left_inverse H₁ H₂,
  iff.intro
    (strictly_decreasing_of_strictly_decreasing_comp_left H₁ H₃)
    (λ H, strictly_decreasing_comp_dec_inc H H₂)
end

/- composition rules for weak orders -/

section
  variables [weak_order A] [weak_order B] [weak_order C]

  theorem nondecreasing_of_nondecreasing_comp_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : nondecreasing h) (H₃ : nondecreasing (g ∘ f)) :
    nondecreasing f :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  have h (g (f a₁)) ≤ h (g (f a₂)), from H₂ (H₃ this),
  show f a₁ ≤ f a₂, by rewrite *H₁ at this; apply this

  theorem nonincreasing_of_nondecreasing_comp_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : nonincreasing h) (H₃ : nondecreasing (g ∘ f)) :
    nonincreasing f :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  have h (g (f a₁)) ≥ h (g (f a₂)), from H₂ (H₃ this),
  show f a₁ ≥ f a₂, by rewrite *H₁ at this; apply this

  theorem nonincreasing_of_nonincreasing_comp_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : nondecreasing h) (H₃ : nonincreasing (g ∘ f)) :
    nonincreasing f :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  have h (g (f a₁)) ≥ h (g (f a₂)), from H₂ (H₃ this),
  show f a₁ ≥ f a₂, by rewrite *H₁ at this; apply this

  theorem nondecreasing_of_nonincreasing_comp_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : nonincreasing h) (H₃ : nonincreasing (g ∘ f)) :
    nondecreasing f :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  have h (g (f a₁)) ≤ h (g (f a₂)), from H₂ (H₃ this),
  show f a₁ ≤ f a₂, by rewrite *H₁ at this; apply this

  theorem nondecreasing_of_nondecreasing_comp_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : nondecreasing h) (H₃ : nondecreasing (g ∘ f)) :
    nondecreasing g :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  have g (f (h a₁)) ≤ g (f (h a₂)), from H₃ (H₂ this),
  show g a₁ ≤ g a₂, by rewrite *H₁ at this; apply this

  theorem nonincreasing_of_nondecreasing_comp_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : nonincreasing h) (H₃ : nondecreasing (g ∘ f)) :
    nonincreasing g :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  have g (f (h a₁)) ≥ g (f (h a₂)), from H₃ (H₂ this),
  show g a₁ ≥ g a₂, by rewrite *H₁ at this; apply this

  theorem nondecreasing_of_nonincreasing_comp_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : nonincreasing h) (H₃ : nonincreasing (g ∘ f)) :
    nondecreasing g :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  have g (f (h a₁)) ≤ g (f (h a₂)), from H₃ (H₂ this),
  show g a₁ ≤ g a₂, by rewrite *H₁ at this; apply this

  theorem nonincreasing_of_nonincreasing_comp_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : nondecreasing h) (H₃ : nonincreasing (g ∘ f)) :
    nonincreasing g :=
  take a₁ a₂, suppose a₁ ≤ a₂,
  have g (f (h a₁)) ≥ g (f (h a₂)), from H₃ (H₂ this),
  show g a₁ ≥ g a₂, by rewrite *H₁ at this; apply this
end

section
  variables [weak_order A] [linear_strong_order_pair B] [linear_strong_order_pair C]

  theorem nondecreasing_comp_iff_nondecreasing_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_increasing h) :
    nondecreasing (g ∘ f) ↔ nondecreasing f :=
  have H₃ : nondecreasing g, from nondecreasing_of_left_inverse H₁ H₂,
  iff.intro
    (nondecreasing_of_nondecreasing_comp_right H₁ (nondecreasing_of_strictly_increasing H₂))
    (nondecreasing_comp_nondec_nondec H₃)

  theorem nondecreasing_comp_iff_nonincreasing_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_decreasing h) :
    nondecreasing (g ∘ f) ↔ nonincreasing f :=
  have H₃ : nonincreasing g, from nonincreasing_of_left_inverse H₁ H₂,
  iff.intro
    (nonincreasing_of_nondecreasing_comp_right H₁ (nonincreasing_of_strictly_decreasing H₂))
    (nondecreasing_comp_noninc_noninc H₃)

  theorem nonincreasing_comp_iff_nonincreasing_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_increasing h) :
    nonincreasing (g ∘ f) ↔ nonincreasing f :=
  have H₃ : nondecreasing g, from nondecreasing_of_left_inverse H₁ H₂,
  iff.intro
    (nonincreasing_of_nonincreasing_comp_right H₁ (nondecreasing_of_strictly_increasing H₂))
    (nonincreasing_comp_nondec_noninc H₃)

  theorem nonincreasing_comp_iff_nondecreasing_right {g : B → C} {f : A → B} {h : C → B}
      (H₁ : left_inverse h g) (H₂ : strictly_decreasing h) :
    nonincreasing (g ∘ f) ↔ nondecreasing f :=
  have H₃ : nonincreasing g, from nonincreasing_of_left_inverse H₁ H₂,
  iff.intro
    (nondecreasing_of_nonincreasing_comp_right H₁ (nonincreasing_of_strictly_decreasing H₂))
    (nonincreasing_comp_noninc_nondec H₃)
end

section
  variables [linear_strong_order_pair A] [linear_strong_order_pair B] [weak_order C]

  theorem nondecreasing_comp_iff_nondecreasing_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_increasing f) :
    nondecreasing (g ∘ f) ↔ nondecreasing g :=
  have H₃ : nondecreasing h, from nondecreasing_of_left_inverse H₁ H₂,
  iff.intro
    (nondecreasing_of_nondecreasing_comp_left H₁ H₃)
    (λ H, nondecreasing_comp_nondec_nondec H (nondecreasing_of_strictly_increasing H₂))

  theorem nondecreasing_comp_iff_nonincreasing_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_decreasing f) :
    nondecreasing (g ∘ f) ↔ nonincreasing g :=
  have H₃ : nonincreasing h, from nonincreasing_of_left_inverse H₁ H₂,
  iff.intro
    (nonincreasing_of_nondecreasing_comp_left H₁ H₃)
    (λ H, nondecreasing_comp_noninc_noninc H (nonincreasing_of_strictly_decreasing H₂))

  theorem nonincreasing_comp_iff_nondecreasing_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_decreasing f) :
    nonincreasing (g ∘ f) ↔ nondecreasing g :=
  have H₃ : nonincreasing h, from nonincreasing_of_left_inverse H₁ H₂,
  iff.intro
    (nondecreasing_of_nonincreasing_comp_left H₁ H₃)
    (λ H, nonincreasing_comp_nondec_noninc H (nonincreasing_of_strictly_decreasing H₂))

  theorem nonincreasing_comp_iff_nonincreasing_left {g : B → C} {f : A → B} {h : B → A}
      (H₁ : left_inverse f h) (H₂ : strictly_increasing f) :
    nonincreasing (g ∘ f) ↔ nonincreasing g :=
  have H₃ : nondecreasing h, from nondecreasing_of_left_inverse H₁ H₂,
  iff.intro
    (nonincreasing_of_nonincreasing_comp_left H₁ H₃)
    (λ H, nonincreasing_comp_noninc_nondec H (nondecreasing_of_strictly_increasing H₂))
end
