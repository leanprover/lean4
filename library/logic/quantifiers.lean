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
