-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad

import logic.connectives logic.nonempty

open inhabited nonempty

inductive Exists {A : Type} (P : A → Prop) : Prop :=
intro : ∀ (a : A), P a → Exists P

definition exists_intro := @Exists.intro

notation `exists` binders `,` r:(scoped P, Exists P) := r
notation `∃` binders `,` r:(scoped P, Exists P) := r

theorem exists_elim {A : Type} {p : A → Prop} {B : Prop} (H1 : ∃x, p x) (H2 : ∀ (a : A) (H : p a), B) : B :=
Exists.rec H2 H1

theorem exists_not_forall {A : Type} {p : A → Prop} (H : ∃x, p x) : ¬∀x, ¬p x :=
assume H1 : ∀x, ¬p x,
  obtain (w : A) (Hw : p w), from H,
  absurd Hw (H1 w)

theorem forall_not_exists {A : Type} {p : A → Prop} (H2 : ∀x, p x) : ¬∃x, ¬p x :=
assume H1 : ∃x, ¬p x,
  obtain (w : A) (Hw : ¬p w), from H1,
  absurd (H2 w) Hw

definition exists_unique {A : Type} (p : A → Prop) :=
∃x, p x ∧ ∀y, p y → y = x

notation `∃!` binders `,` r:(scoped P, exists_unique P) := r

theorem exists_unique_intro {A : Type} {p : A → Prop} (w : A) (H1 : p w) (H2 : ∀y, p y → y = w) : ∃!x, p x :=
exists_intro w (and.intro H1 H2)

theorem exists_unique_elim {A : Type} {p : A → Prop} {b : Prop}
                           (H2 : ∃!x, p x) (H1 : ∀x, p x → (∀y, p y → y = x) → b) : b :=
obtain w Hw, from H2,
H1 w (and.elim_left Hw) (and.elim_right Hw)

theorem forall_congr {A : Type} {φ ψ : A → Prop} (H : ∀x, φ x ↔ ψ x) : (∀x, φ x) ↔ (∀x, ψ x) :=
iff.intro
  (assume Hl, take x, iff.elim_left (H x) (Hl x))
  (assume Hr, take x, iff.elim_right (H x) (Hr x))

theorem exists_congr {A : Type} {φ ψ : A → Prop} (H : ∀x, φ x ↔ ψ x) : (∃x, φ x) ↔ (∃x, ψ x) :=
iff.intro
  (assume Hex, obtain w Pw, from Hex,
    exists_intro w (iff.elim_left (H w) Pw))
  (assume Hex, obtain w Qw, from Hex,
    exists_intro w (iff.elim_right (H w) Qw))

theorem forall_true_iff_true (A : Type) : (∀x : A, true) ↔ true :=
iff.intro (assume H, trivial) (assume H, take x, trivial)

theorem forall_p_iff_p (A : Type) {H : inhabited A} (p : Prop) : (∀x : A, p) ↔ p :=
iff.intro (assume Hl, inhabited.destruct H (take x, Hl x)) (assume Hr, take x, Hr)

theorem exists_p_iff_p (A : Type) {H : inhabited A} (p : Prop) : (∃x : A, p) ↔ p :=
iff.intro
  (assume Hl, obtain a Hp, from Hl, Hp)
  (assume Hr, inhabited.destruct H (take a, exists_intro a Hr))

theorem forall_and_distribute {A : Type} (φ ψ : A → Prop) : (∀x, φ x ∧ ψ x) ↔ (∀x, φ x) ∧ (∀x, ψ x) :=
iff.intro
  (assume H, and.intro (take x, and.elim_left (H x)) (take x, and.elim_right (H x)))
  (assume H, take x, and.intro (and.elim_left H x) (and.elim_right H x))

theorem exists_or_distribute {A : Type} (φ ψ : A → Prop) : (∃x, φ x ∨ ψ x) ↔ (∃x, φ x) ∨ (∃x, ψ x) :=
iff.intro
  (assume H, obtain (w : A) (Hw : φ w ∨ ψ w), from H,
    or.elim Hw
      (assume Hw1 : φ w, or.inl (exists_intro w Hw1))
      (assume Hw2 : ψ w, or.inr (exists_intro w Hw2)))
  (assume H, or.elim H
    (assume H1, obtain (w : A) (Hw : φ w), from H1,
      exists_intro w (or.inl Hw))
    (assume H2, obtain (w : A) (Hw : ψ w), from H2,
      exists_intro w (or.inr Hw)))

theorem exists_imp_nonempty {A : Type} {P : A → Prop} (H : ∃x, P x) : nonempty A :=
obtain w Hw, from H, nonempty.intro w
