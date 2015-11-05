/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

Universal and existential quantifiers. See also init.logic.
-/
import .connectives
open inhabited nonempty

theorem exists_imp_distrib {A : Type} {B : Prop} {P : A → Prop} : ((∃ a : A, P a) → B) ↔ (∀ a : A, P a → B) :=
iff.intro (λ e x H, e (exists.intro x H)) Exists.rec

theorem forall_iff_not_exists {A : Type} {P : A → Prop} : (¬ ∃ a : A, P a) ↔ ∀ a : A, ¬ P a :=
exists_imp_distrib

theorem not_forall_not_of_exists {A : Type} {p : A → Prop} (H : ∃ x, p x) : ¬ ∀ x, ¬ p x :=
assume H1 : ∀ x, ¬ p x,
  obtain (w : A) (Hw : p w), from H,
  absurd Hw (H1 w)

theorem not_exists_not_of_forall {A : Type} {p : A → Prop} (H2 : ∀ x, p x) : ¬ ∃ x, ¬p x :=
assume H1 : ∃ x, ¬ p x,
  obtain (w : A) (Hw : ¬ p w), from H1,
  absurd (H2 w) Hw

theorem not_forall_of_exists_not {A : Type} {P : A → Prop} (H : ∃ a : A, ¬ P a) : ¬ ∀ a : A, P a :=
assume H', not_exists_not_of_forall H' H

theorem forall_congr {A : Type} {φ ψ : A → Prop} : (∀ x, φ x ↔ ψ x) → ((∀ x, φ x) ↔ (∀ x, ψ x)) :=
forall_iff_forall

theorem exists_congr {A : Type} {φ ψ : A → Prop} : (∀ x, φ x ↔ ψ x) → ((∃ x, φ x) ↔ (∃ x, ψ x)) :=
exists_iff_exists

theorem forall_true_iff_true (A : Type) : (∀ x : A, true) ↔ true :=
iff_true_intro (λH, trivial)

theorem forall_p_iff_p (A : Type) [H : inhabited A] (p : Prop) : (∀ x : A, p) ↔ p :=
iff.intro (inhabited.destruct H) (λ Hr x, Hr)

theorem exists_p_iff_p (A : Type) [H : inhabited A] (p : Prop) : (∃ x : A, p) ↔ p :=
iff.intro (Exists.rec (λ x Hp, Hp)) (inhabited.destruct H exists.intro)

theorem forall_and_distribute {A : Type} (φ ψ : A → Prop) :
  (∀ x, φ x ∧ ψ x) ↔ (∀ x, φ x) ∧ (∀ x, ψ x) :=
iff.intro
  (assume H, and.intro (take x, and.left (H x)) (take x, and.right (H x)))
  (assume H x, and.intro (and.left H x) (and.right H x))

theorem exists_or_distribute {A : Type} (φ ψ : A → Prop) :
  (∃ x, φ x ∨ ψ x) ↔ (∃ x, φ x) ∨ (∃ x, ψ x) :=
iff.intro
  (Exists.rec (λ x, or.imp !exists.intro !exists.intro))
  (or.rec (exists_imp_exists (λ x, or.inl))
          (exists_imp_exists (λ x, or.inr)))

section
  open decidable eq.ops

  variables {A : Type} (P : A → Prop) (a : A) [H : decidable (P a)]
  include H

  definition decidable_forall_eq [instance] : decidable (∀ x, x = a → P x) :=
  if pa : P a then inl (λ x heq, eq.substr heq pa)
  else inr (not.mto (λH, H a rfl) pa)

  definition decidable_exists_eq [instance] : decidable (∃ x, x = a ∧ P x) :=
  if pa : P a then inl (exists.intro a (and.intro rfl pa))
  else inr (Exists.rec (λh, and.rec (λheq, eq.substr heq pa)))
end

/- exists_unique -/

definition exists_unique {A : Type} (p : A → Prop) :=
∃x, p x ∧ ∀y, p y → y = x

notation `∃!` binders `, ` r:(scoped P, exists_unique P) := r

theorem exists_unique.intro {A : Type} {p : A → Prop} (w : A) (H1 : p w) (H2 : ∀y, p y → y = w) :
  ∃!x, p x :=
exists.intro w (and.intro H1 H2)

theorem exists_unique.elim {A : Type} {p : A → Prop} {b : Prop}
    (H2 : ∃!x, p x) (H1 : ∀x, p x → (∀y, p y → y = x) → b) : b :=
obtain w Hw, from H2,
H1 w (and.left Hw) (and.right Hw)

theorem exists_unique_of_exists_of_unique {A : Type} {p : A → Prop}
    (Hex : ∃ x, p x) (Hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) :
  ∃! x, p x :=
obtain x px, from Hex,
exists_unique.intro x px (take y, suppose p y, show y = x, from !Hunique this px)

theorem exists_of_exists_unique {A : Type} {p : A → Prop} (H : ∃! x, p x) :
  ∃ x, p x :=
obtain x Hx, from H,
exists.intro x (and.left Hx)

theorem unique_of_exists_unique {A : Type} {p : A → Prop}
    (H : ∃! x, p x) {y₁ y₂ : A} (py₁ : p y₁) (py₂ : p y₂) :
  y₁ = y₂ :=
exists_unique.elim H
  (take x, suppose p x,
    assume unique : ∀ y, p y → y = x,
    show y₁ = y₂, from eq.trans (unique _ py₁) (eq.symm (unique _ py₂)))

/- definite description -/

section
  open classical

  noncomputable definition the {A : Type} {p : A → Prop} (H : ∃! x, p x) : A :=
  some (exists_of_exists_unique H)

  theorem the_spec {A : Type} {p : A → Prop} (H : ∃! x, p x) : p (the H) :=
  some_spec (exists_of_exists_unique H)

  theorem eq_the {A : Type} {p : A → Prop} (H : ∃! x, p x) {y : A} (Hy : p y) :
    y = the H :=
  unique_of_exists_unique H Hy (the_spec H)
end

/- congruences -/

section
  variables {A : Type} {p₁ p₂ : A → Prop} (H : ∀ x, p₁ x ↔ p₂ x)

  theorem congr_forall [congr] : (∀ x, p₁ x) ↔ (∀ x, p₂ x) :=
  forall_congr H

  theorem congr_exists [congr] : (∃ x, p₁ x) ↔ (∃ x, p₂ x) :=
  exists_congr H

  include H
  theorem congr_exists_unique [congr] : (∃! x, p₁ x) ↔ (∃! x, p₂ x) :=
   congr_exists (λx, congr_and (H x) (congr_forall
     (λy, congr_imp (H y) iff.rfl)))
end

/- We add this attribute again here so that the simplifier finds it before [congr_forall] -/
attribute congr_imp [congr]
