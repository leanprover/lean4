/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.set.function
Author: Jeremy Avigad, Andrew Zipperer

Functions between subsets of finite types.
-/
import .basic
import algebra.function
open function eq.ops

namespace set
  variables {X Y Z : Type}

  abbreviation eq_on (f1 f2 : X → Y) (a : set X) : Prop :=
  ∀₀ x ∈ a, f1 x = f2 x

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

  definition maps_to (f : X → Y) (a : set X) (b : set Y) : Prop := ∀⦃x⦄, x ∈ a → f x ∈ b

  theorem maps_to_compose {g : Y → Z} {f : X → Y} {a : set X} {b : set Y} {c : set Z}
     (H1 : maps_to g b c) (H2 : maps_to f a b) : maps_to (g ∘ f) a c :=
  take x, assume H : x ∈ a, H1 (H2 H)

  definition inj_on (f : X → Y) (a : set X) : Prop :=
  ∀⦃x1 x2 : X⦄, x1 ∈ a → x2 ∈ a → f x1 = f x2 → x1 = x2

  theorem inj_on_of_eq_on {f1 f2 : X → Y} {a : set X} (inj_f1 : inj_on f1 a)
      (eq_f1_f2 : eq_on f1 f2 a) : inj_on f2 a :=
  take x1 x2 : X,
  assume ax1 : x1 ∈ a,
  assume ax2 : x2 ∈ a,
  assume H : f2 x1 = f2 x2,
  have H' : f1 x1 = f1 x2, from eq_f1_f2 ax1 ⬝ H ⬝ (eq_f1_f2 ax2)⁻¹,
  show x1 = x2, from inj_f1 ax1 ax2 H'

  definition surj_on (f : X → Y) (a : set X) (b : set Y) : Prop := b ⊆ f '[a]

  theorem surj_on_of_eq_on {f1 f2 : X → Y} {a : set X} {b : set Y} (surj_f1 : surj_on f1 a b)
      (eq_f1_f2 : eq_on f1 f2 a) : surj_on f2 a b :=
  take y, assume H : y ∈ b,
  obtain x (H1 : x ∈ a ∧ f1 x = y), from surj_f1 H,
  have H2 : x ∈ a, from and.left H1,
  have H3 : f2 x = y, from (eq_f1_f2 H2)⁻¹ ⬝ and.right H1,
  exists.intro x (and.intro H2 H3)
end set
