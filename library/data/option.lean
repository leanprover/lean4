/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

import logic.eq
open eq.ops decidable

namespace option
  definition is_none {A : Type} : option A →  Prop
  | none     := true
  | (some v) := false

  theorem is_none_none {A : Type} : is_none (@none A) :=
  trivial

  theorem not_is_none_some {A : Type} (a : A) : ¬ is_none (some a) :=
  not_false

  theorem none_ne_some {A : Type} (a : A) : none ≠ some a :=
  by contradiction

  theorem some.inj {A : Type} {a₁ a₂ : A} (H : some a₁ = some a₂) : a₁ = a₂ :=
  by injection H; assumption

  protected definition is_inhabited [instance] (A : Type) : inhabited (option A) :=
  inhabited.mk none

  protected definition has_decidable_eq [instance] {A : Type} [H : decidable_eq A] : ∀ o₁ o₂ : option A, decidable (o₁ = o₂)
  | none      none      := by left;  reflexivity
  | none      (some v₂) := by right; contradiction
  | (some v₁) none      := by right; contradiction
  | (some v₁) (some v₂) :=
    match H v₁ v₂ with
    | inl e := by left; congruence; assumption
    | inr n := by right; intro h; injection h; contradiction
    end
end option
