module

prelude
import Init.Core
import Init.Data.Ord
import Init.Data.List.Lex

namespace Std.Classes.Test

class BLT (α : Type u) where
  LT : α → α → Bool

class LawfulBLT (α : Type u) [LT α] [BLT α] where
  lt_iff_lt : ∀ a b : α, LT.lt a b ↔ BLT.LT a b

instance [LT α] [BLT α] [LawfulBLT α] : DecidableLT α :=
  fun a b => if h : BLT.LT a b then .isTrue (LawfulBLT.lt_iff_lt .. |>.mpr h) else .isFalse (h.imp (LawfulBLT.lt_iff_lt ..).mp)

class BLE (α : Type u) where
  LE : α → α → Bool

class LawfulBLE (α : Type u) [LE α] [BLE α] where
  le_iff_le : ∀ a b : α, LE.le a b ↔ BLE.LE a b

instance [LE α] [BLE α] [LawfulBLE α] : DecidableLE α :=
  fun a b => if h : BLE.LE a b then .isTrue (LawfulBLE.le_iff_le .. |>.mpr h) else .isFalse (h.imp (LawfulBLE.le_iff_le ..).mp)

class Preorder (α : Type u) extends LT α, LE α, BLT α, BLE α, BEq α where

class LEDefinedPreorder (α : Type u) [Preorder α] where
  lt_iff_le_not_ge : ∀ a b : α, LT.lt a b ↔ LE.le a b ∧ ¬ LE.le b a := by intros; rfl

class Reflexive (α : Type u) [LE α] where
  refl : ∀ a : α, LE.le a a

class LawfulPreorder (α : Type u) [Preorder α] extends
    LawfulBLT α, LawfulBLE α, LEDefinedPreorder α, Reflexive α where
  le_trans : ∀ a b c : α, LE.le a b → LE.le b c → LE.le a c
  le_le_iff_beq : ∀ a b : α, a < b ∧ b < a ↔ a == b

class PartialOrder (α : Type u) extends Preorder α

class LawfulPartialOrder (α : Type u) [PartialOrder α] extends LawfulPreorder α, LawfulBEq α

class OrientedOrd (α : Type u) extends Ord α, Preorder α

class LawfulOrientedOrd (α : Type u) [OrientedOrd α] where
  compare_eq_lt_iff_lt : ∀ a b : α, compare a b = .lt ↔ LT.lt a b
  compare_isLE_iff_le : ∀ a b : α, (compare a b).isLE ↔ LE.le a b
  compare_isGE_iff_ge : ∀ a b : α, (compare a b).isGE ↔ LE.le b a

class LinearPreorder (α : Type u) extends Min α, Max α, OrientedOrd α -- should merge this with OrientedOrd

class LawfulLinearPreorder (α : Type u) [LinearPreorder α] extends
    LawfulPreorder α, LawfulOrientedOrd α where
  min_eq : ∀ a b : α, min a b = minOfLe.min a b
  max_eq : ∀ a b : α, max a b = maxOfLe.max a b

class LinearOrder (α : Type u) extends LinearPreorder α, PartialOrder α

class LawfulLinearOrder (α : Type u) [LinearOrder α] extends
    LawfulLinearPreorder α, LawfulPartialOrder α

section SimpLemmas

-- TODO: simp lemmas for the different kinds of order structures

end SimpLemmas

section Demo

open _root_.List

theorem irrefl {α : Type u} [Preorder α] [LawfulPreorder α] (a : α) : ¬ a < a := by
  sorry

theorem asymm [Preorder α] [LawfulPreorder α] (a b : α) : a < b → ¬ b < a := by
  sorry

theorem lt_antisymm [PartialOrder α] [LawfulPartialOrder α] (a b : α) : ¬ a < b → ¬ b < a → a = b := by
  sorry

protected theorem List.le_iff_exists [PartialOrder α] [LawfulPartialOrder α] {l₁ l₂ : List α} :
    l₁ ≤ l₂ ↔
      (l₁ = l₂.take l₁.length) ∨
        (∃ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
          (∀ j, (hj : j < i) →
            l₁[j]'(Nat.lt_trans hj h₁) = l₂[j]'(Nat.lt_trans hj h₂)) ∧ l₁[i] < l₂[i]) := by
  open Classical in
  rw [← lex_eq_false_iff_ge, lex_eq_false_iff_exists]
  · simp only [isEqv_eq, beq_iff_eq, decide_eq_true_eq]
    simp only [eq_comm]
    conv => lhs; simp +singlePass [exists_comm]
  · simpa using irrefl
  · simpa using asymm
  · simpa using lt_antisymm

protected theorem List.map_le
    [LinearOrder α] [LawfulLinearOrder α] [LinearOrder β] [LawfulLinearOrder β]
    {l₁ l₂ : List α} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : l₁ ≤ l₂) :
    map f l₁ ≤ map f l₂ := by
  rw [List.le_iff_exists] at h ⊢
  obtain (h | ⟨i, h₁, h₂, w₁, w₂⟩) := h
  · left
    rw [h]
    simp
  · right
    refine ⟨i, by simpa using h₁, by simpa using h₂, ?_, ?_⟩
    · simp +contextual [w₁]
    · simpa using w _ _ w₂

end Demo

end Std.Classes.Test
