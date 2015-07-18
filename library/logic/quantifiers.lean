/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

Universal and existential quantifiers. See also init.logic.
-/
import .connectives
open inhabited nonempty

theorem not_forall_not_of_exists {A : Type} {p : A → Prop} (H : ∃x, p x) : ¬∀x, ¬p x :=
assume H1 : ∀x, ¬p x,
  obtain (w : A) (Hw : p w), from H,
  absurd Hw (H1 w)

theorem not_exists_not_of_forall {A : Type} {p : A → Prop} (H2 : ∀x, p x) : ¬∃x, ¬p x :=
assume H1 : ∃x, ¬p x,
  obtain (w : A) (Hw : ¬p w), from H1,
  absurd (H2 w) Hw

theorem forall_congr {A : Type} {φ ψ : A → Prop} (H : ∀x, φ x ↔ ψ x) : (∀x, φ x) ↔ (∀x, ψ x) :=
iff.intro
  (assume Hl, take x, iff.elim_left (H x) (Hl x))
  (assume Hr, take x, iff.elim_right (H x) (Hr x))

theorem exists_congr {A : Type} {φ ψ : A → Prop} (H : ∀x, φ x ↔ ψ x) : (∃x, φ x) ↔ (∃x, ψ x) :=
iff.intro
  (assume Hex, obtain w Pw, from Hex,
    exists.intro w (iff.elim_left (H w) Pw))
  (assume Hex, obtain w Qw, from Hex,
    exists.intro w (iff.elim_right (H w) Qw))

theorem forall_true_iff_true (A : Type) : (∀x : A, true) ↔ true :=
iff.intro (assume H, trivial) (assume H, take x, trivial)

theorem forall_p_iff_p (A : Type) [H : inhabited A] (p : Prop) : (∀x : A, p) ↔ p :=
iff.intro (assume Hl, inhabited.destruct H (take x, Hl x)) (assume Hr, take x, Hr)

theorem exists_p_iff_p (A : Type) [H : inhabited A] (p : Prop) : (∃x : A, p) ↔ p :=
iff.intro
  (assume Hl, obtain a Hp, from Hl, Hp)
  (assume Hr, inhabited.destruct H (take a, exists.intro a Hr))

theorem forall_and_distribute {A : Type} (φ ψ : A → Prop) :
  (∀x, φ x ∧ ψ x) ↔ (∀x, φ x) ∧ (∀x, ψ x) :=
iff.intro
  (assume H, and.intro (take x, and.elim_left (H x)) (take x, and.elim_right (H x)))
  (assume H, take x, and.intro (and.elim_left H x) (and.elim_right H x))

theorem exists_or_distribute {A : Type} (φ ψ : A → Prop) :
  (∃x, φ x ∨ ψ x) ↔ (∃x, φ x) ∨ (∃x, ψ x) :=
iff.intro
  (assume H, obtain (w : A) (Hw : φ w ∨ ψ w), from H,
    or.elim Hw
      (assume Hw1 : φ w, or.inl (exists.intro w Hw1))
      (assume Hw2 : ψ w, or.inr (exists.intro w Hw2)))
  (assume H, or.elim H
    (assume H1, obtain (w : A) (Hw : φ w), from H1,
      exists.intro w (or.inl Hw))
    (assume H2, obtain (w : A) (Hw : ψ w), from H2,
      exists.intro w (or.inr Hw)))

theorem nonempty_of_exists {A : Type} {P : A → Prop} (H : ∃x, P x) : nonempty A :=
obtain w Hw, from H, nonempty.intro w

section
  open decidable eq.ops

  variables {A : Type} (P : A → Prop) (a : A) [H : decidable (P a)]
  include H

  definition decidable_forall_eq [instance] : decidable (∀ x, x = a → P x) :=
  decidable.rec_on H
     (λ pa,  inl (λ x heq, eq.rec_on (eq.rec_on heq rfl) pa))
     (λ npa, inr (λ h, absurd (h a rfl) npa))

  definition decidable_exists_eq [instance] : decidable (∃ x, x = a ∧ P x) :=
  decidable.rec_on H
     (λ pa, inl (exists.intro a (and.intro rfl pa)))
     (λ npa, inr (λ h,
       obtain (w : A) (Hw : w = a ∧ P w), from h,
       absurd (and.rec_on Hw (λ h₁ h₂, h₁ ▸ h₂)) npa))
end

/- exists_unique -/

definition exists_unique {A : Type} (p : A → Prop) :=
∃x, p x ∧ ∀y, p y → y = x

notation `∃!` binders `,` r:(scoped P, exists_unique P) := r

theorem exists_unique.intro {A : Type} {p : A → Prop} (w : A) (H1 : p w) (H2 : ∀y, p y → y = w) :
  ∃!x, p x :=
exists.intro w (and.intro H1 H2)

theorem exists_unique.elim {A : Type} {p : A → Prop} {b : Prop}
    (H2 : ∃!x, p x) (H1 : ∀x, p x → (∀y, p y → y = x) → b) : b :=
obtain w Hw, from H2,
H1 w (and.elim_left Hw) (and.elim_right Hw)

/- congruences -/

section
  variables {A : Type} {p₁ p₂ : A → Prop} (H : ∀x, p₁ x ↔ p₂ x)

  theorem congr_forall : (∀x, p₁ x) ↔ (∀x, p₂ x) :=
  iff.intro
    (assume H', take x, iff.mp (H x) (H' x))
    (assume H', take x, iff.mpr (H x) (H' x))

  theorem congr_exists : (∃x, p₁ x) ↔ (∃x, p₂ x) :=
  iff.intro
    (assume H', exists.elim H' (λ x H₁, exists.intro x (iff.mp (H x) H₁)))
    (assume H', exists.elim H' (λ x H₁, exists.intro x (iff.mpr (H x) H₁)))

  include H
  theorem congr_exists_unique : (∃!x, p₁ x) ↔ (∃!x, p₂ x) :=
  begin
    apply congr_exists,
    intro x,
    apply congr_and (H x),
    apply congr_forall,
    intro y,
    apply congr_imp (H y) !iff.rfl
  end
end
