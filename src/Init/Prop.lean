/-
Copyright (c) 2024 Lean FRO.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro

This provides additional lemmas about propositional types beyond what is
needed for Core and SimpLemmas.
-/
prelude
import Init.SimpLemmas
set_option linter.missingDocs true -- keep it documented

/-! ## not -/

theorem not_not_em (a : Prop) : ¬¬(a ∨ ¬a) := fun h => h (.inr (h ∘ .inl))

/-! ## and -/

-- TODO: rename and_self to and_self_eq
theorem and_self_iff : a ∧ a ↔ a := Iff.of_eq (and_self a)
theorem and_not_self_iff (a : Prop) : a ∧ ¬a ↔ False := iff_false_intro and_not_self
theorem not_and_self_iff (a : Prop) : ¬a ∧ a ↔ False := iff_false_intro not_and_self

theorem And.imp (f : a → c) (g : b → d) (h : a ∧ b) : c ∧ d :=  And.intro (f h.left) (g h.right)
theorem And.imp_left (h : a → b) : a ∧ c → b ∧ c := .imp h id
theorem And.imp_right (h : a → b) : c ∧ a → c ∧ b := .imp id h

theorem and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d :=
  Iff.intro (And.imp h₁.mp h₂.mp) (And.imp h₁.mpr h₂.mpr)
theorem and_congr_left' (h : a ↔ b) : a ∧ c ↔ b ∧ c := and_congr h .rfl
theorem and_congr_right' (h : b ↔ c) : a ∧ b ↔ a ∧ c := and_congr .rfl h

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) := mt And.left
theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) := mt And.right

theorem and_congr_right_eq (h : a → b = c) : (a ∧ b) = (a ∧ c) := propext (and_congr_right (Iff.of_eq ∘ h))
theorem and_congr_left_eq  (h : c → a = b) : (a ∧ c) = (b ∧ c) := propext (and_congr_left  (Iff.of_eq ∘ h))

theorem and_left_comm : a ∧ b ∧ c ↔ b ∧ a ∧ c :=
  Iff.intro (fun ⟨ha, hb, hc⟩ => ⟨hb, ha, hc⟩)
            (fun ⟨hb, ha, hc⟩ => ⟨ha, hb, hc⟩)

theorem and_right_comm : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b :=
  Iff.intro (fun ⟨⟨ha, hb⟩, hc⟩ => ⟨⟨ha, hc⟩, hb⟩)
            (fun ⟨⟨ha, hc⟩, hb⟩ => ⟨⟨ha, hb⟩, hc⟩)

theorem and_rotate : a ∧ b ∧ c ↔ b ∧ c ∧ a := by rw [and_left_comm, @and_comm a c]
theorem and_and_and_comm : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by rw [← and_assoc, @and_right_comm a, and_assoc]
theorem and_and_left  : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by rw [and_and_and_comm, and_self]
theorem and_and_right : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b ∧ c := by rw [and_and_and_comm, and_self]

theorem and_iff_left  (hb : b) : a ∧ b ↔ a := Iff.intro And.left  (And.intro · hb)
theorem and_iff_right (ha : a) : a ∧ b ↔ b := Iff.intro And.right (And.intro ha ·)

/-! ## or -/

theorem or_self_iff : a ∨ a ↔ a := or_self _ ▸ .rfl
theorem not_or_intro {a b : Prop} (ha : ¬a) (hb : ¬b) : ¬(a ∨ b) := (·.elim ha hb)

theorem Or.resolve_left  (h: a ∨ b) (na : ¬a) : b := h.elim (absurd · na) id
theorem Or.resolve_right (h: a ∨ b) (nb : ¬b) : a := h.elim id (absurd · nb)

theorem Or.neg_resolve_left  (h : ¬a ∨ b) (ha : a) : b := h.elim (absurd ha) id
theorem Or.neg_resolve_right (h : a ∨ ¬b) (nb : b) : a := h.elim id (absurd nb)

theorem or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) := ⟨.imp h₁.1 h₂.1, .imp h₁.2 h₂.2⟩
theorem or_congr_left (h : a ↔ b) : a ∨ c ↔ b ∨ c := or_congr h .rfl
theorem or_congr_right (h : b ↔ c) : a ∨ b ↔ a ∨ c := or_congr .rfl h

theorem or_left_comm  : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) := by rw [← or_assoc, ← or_assoc, @or_comm a b]
theorem or_right_comm : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by rw [or_assoc, or_assoc, @or_comm b]

theorem or_or_or_comm : (a ∨ b) ∨ c ∨ d ↔ (a ∨ c) ∨ b ∨ d := by rw [← or_assoc, @or_right_comm a, or_assoc]

theorem or_or_distrib_left : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by rw [or_or_or_comm, or_self]
theorem or_or_distrib_right : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by rw [or_or_or_comm, or_self]

theorem or_rotate : a ∨ b ∨ c ↔ b ∨ c ∨ a := by simp only [or_left_comm, Or.comm]

theorem or_iff_left (hb : ¬b) : a ∨ b ↔ a := or_iff_left_iff_imp.2 hb.elim
theorem or_iff_right (ha : ¬a) : a ∨ b ↔ b := or_iff_right_iff_imp.2 ha.elim

/-! ## distributivity -/

theorem not_imp_of_and_not : a ∧ ¬b → ¬(a → b)
  | ⟨ha, hb⟩, h => hb <| h ha

theorem imp_and {α} : (α → b ∧ c) ↔ (α → b) ∧ (α → c) :=
  ⟨fun h => ⟨fun ha => (h ha).1, fun ha => (h ha).2⟩, fun h ha => ⟨h.1 ha, h.2 ha⟩⟩

theorem not_and' : ¬(a ∧ b) ↔ b → ¬a := Iff.trans not_and imp_not_comm

/-- `∧` distributes over `∨` (on the left). -/
theorem and_or_left : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
  Iff.intro (fun ⟨ha, hbc⟩ => hbc.imp (.intro ha) (.intro ha))
            (Or.rec (.imp_right .inl) (.imp_right .inr))

/-- `∧` distributes over `∨` (on the right). -/
theorem or_and_right : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by rw [@and_comm (a ∨ b), and_or_left, @and_comm c, @and_comm c]

/-- `∨` distributes over `∧` (on the left). -/
theorem or_and_left : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
  Iff.intro (Or.rec (fun ha => ⟨.inl ha, .inl ha⟩) (.imp .inr .inr))
            (And.rec <| .rec (fun _ => .inl ·) (.imp_right ∘ .intro))

/-- `∨` distributes over `∧` (on the right). -/
theorem and_or_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := by rw [@or_comm (a ∧ b), or_and_left, @or_comm c, @or_comm c]

theorem or_imp : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
  Iff.intro (fun h => ⟨h ∘ .inl, h ∘ .inr⟩)
            (fun ⟨ha, hb⟩ => Or.rec ha hb)
theorem not_or : ¬(p ∨ q) ↔ ¬p ∧ ¬q := or_imp


theorem not_and_of_not_or_not (h : ¬a ∨ ¬b) : ¬(a ∧ b) := h.elim (mt (·.1)) (mt (·.2))
