/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ordered.Ring
public import Init.Grind.Ring.CommSolver
import Init.Grind.Ring
@[expose] public section
namespace Lean.Grind.Order

/-- A `Weight` is just an linear ordered additive commutative group. -/
class Weight (ω : Type v) extends Add ω, LE ω, LT ω, BEq ω, LawfulBEq ω where
  [decLe : DecidableLE ω]
  [decLt : DecidableLT ω]

/--
An `Offset` type `α` with weight `ω`.
-/
class Offset (α : Type u) (ω : Type v) [Weight ω] extends LE α, LT α, Std.IsPreorder α, Std.LawfulOrderLT α where
  offset      : α → ω → α
  offset_add  : ∀ (a : α) (k₁ k₂ : ω), offset (offset a k₁) k₂ = offset a (k₁ + k₂)
  offset_le   : ∀ (a b : α) (k : ω),   offset a k ≤ offset b k ↔ a ≤ b
  weight_le   : ∀ (a : α) (k₁ k₂ : ω), offset a k₁ ≤ offset a k₂ → k₁ ≤ k₂
  weight_lt   : ∀ (a : α) (k₁ k₂ : ω), offset a k₁ < offset a k₂ → k₁ < k₂

instance : Weight Nat where
instance : Weight Int where

def Unit.weight : Weight Unit where
  add := fun _ _ => ()
  le := fun _ _ => True
  lt := fun _ _ => False
  decLe := fun _ _ => inferInstanceAs (Decidable True)
  decLt := fun _ _ => inferInstanceAs (Decidable False)

attribute [local instance] Ring.intCast Semiring.natCast in
instance {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Ring α] [Std.IsPreorder α] [OrderedRing α] : Offset α Int where
  offset a k    := a + k
  offset_add    := by intros; rw [Ring.intCast_add, Semiring.add_assoc]
  offset_le     := by intros; rw [← OrderedAdd.add_le_left_iff]
  weight_le     := by
    intro _ _ _ h; replace h := OrderedAdd.add_le_right_iff _ |>.mpr h
    exact OrderedRing.le_of_intCast_le_intCast _ _ h
  weight_lt     := by
    intro _ _ _ h; replace h := OrderedAdd.add_lt_right_iff _ |>.mpr h
    exact OrderedRing.lt_of_intCast_lt_intCast _ _ h

instance : Offset Int Int where
  offset a k    := a + k
  offset_add    := by omega
  offset_le     := by simp
  weight_le     := by simp
  weight_lt     := by simp

instance : Offset Nat Nat where
  offset a k    := a + k
  offset_add    := by omega
  offset_le     := by simp
  weight_le     := by simp
  weight_lt     := by simp
  -- TODO: why did we have to provide the following three fields manually?
  le_refl       := by apply Std.IsPreorder.le_refl
  le_trans      := by apply Std.IsPreorder.le_trans
  lt_iff        := by apply Std.LawfulOrderLT.lt_iff

attribute [local instance] Unit.weight

/-- Dummy `Offset` instance for orders that do not support offsets. -/
def dummyOffset (α : Type u) [LE α] [LT α] [Std.IsPreorder α] [Std.LawfulOrderLT α] : Offset α Unit where
  offset a _ := a
  offset_add _ _ _ := rfl
  offset_le _ _ _ := Iff.rfl
  weight_le _ _ _ _ := True.intro
  weight_lt x _ _ h := by exfalso; exact Preorder.lt_irrefl x h

/-- Dummy `Offset` instance for orders that do not support offsets nor `LT` -/
def dummyOffset' (α : Type u) [LE α] [Std.IsPreorder α] : Offset α Unit where
  lt a b := a ≤ b ∧ ¬ b ≤ a
  lt_iff _ _ := Iff.rfl
  offset a _ := a
  offset_add _ _ _ := rfl
  offset_le _ _ _ := Iff.rfl
  weight_le _ _ _ _ := True.intro
  weight_lt _ _ _ h := by cases h; contradiction

namespace Offset

theorem offset_lt {α ω} [Weight ω] [Offset α ω]
    (a b : α) (k : ω) : offset a k < offset b k ↔ a < b := by
  simp only [Std.LawfulOrderLT.lt_iff]
  constructor
  next =>
    intro ⟨h₁, h₂⟩
    constructor
    next => apply offset_le _ _ _ |>.mp h₁
    next => intro h; have := offset_le _ _ k |>.mpr h; contradiction
  next =>
    intro ⟨h₁, h₂⟩
    constructor
    next => apply offset_le _ _ _ |>.mpr h₁
    next => intro h; have := offset_le _ _ k |>.mp h; contradiction

private theorem add_le_add' {α ω} [Weight ω] [Offset α ω]
    {a b : α} {k₁ k₂ : ω} (k : ω) :
    offset a k₁ ≤ offset b k₂ → offset a (k₁ + k) ≤ offset b (k₂ + k) := by
  intro h; replace h := offset_le _ _ k |>.mpr h
  simp [offset_add] at h; assumption

private theorem add_lt_add' {α ω} [Weight ω] [Offset α ω]
    {a b : α} {k₁ k₂ : ω} (k : ω) :
    offset a k₁ < offset b k₂ → offset a (k₁ + k) < offset b (k₂ + k) := by
  intro h; replace h := offset_lt _ _ k |>.mpr h
  simp [offset_add] at h; assumption

/-!
Helper theorems for asserting equalities, negations
-/
theorem le_of_eq {α} [LE α] [Std.IsPreorder α]
    (a b : α) : a = b → a ≤ b := by
  intro h; subst a; apply Std.IsPreorder.le_refl

theorem le_of_not_le {α} [LE α] [Std.IsLinearPreorder α]
    (a b : α) : ¬ a ≤ b → b ≤ a := by
  intro h
  have := Std.IsLinearPreorder.le_total a b
  cases this; contradiction; assumption

theorem lt_of_not_le {α} [LE α] [LT α] [Std.IsLinearPreorder α] [Std.LawfulOrderLT α]
    (a b : α) : ¬ a ≤ b → b < a := by
  intro h
  rw [Std.LawfulOrderLT.lt_iff]
  have := Std.IsLinearPreorder.le_total a b
  cases this; contradiction; simp [*]

theorem le_of_not_lt {α} [LE α] [LT α] [Std.IsLinearPreorder α] [Std.LawfulOrderLT α]
    (a b : α) : ¬ a < b → b ≤ a := by
  rw [Std.LawfulOrderLT.lt_iff]
  open Classical in
  rw [Classical.not_and_iff_not_or_not, Classical.not_not]
  intro h; cases h
  next =>
    have := Std.IsLinearPreorder.le_total a b
    cases this; contradiction; assumption
  next => assumption

/-!
Transitivity theorems
-/
theorem le_offset_trans₁ {α ω} [Weight ω] [Offset α ω]
    (a b c : α) (k₁ k₂ k₃ k₄ k : ω) :
    k₃ == k₂ + k → offset a k₁ ≤ offset b k₂ → offset b k₃ ≤ offset c k₄ → offset a (k₁ + k) ≤ offset c k₄ := by
  intro h h₁ h₂; simp at h; subst k₃
  replace h₁ := add_le_add' k h₁
  exact Std.le_trans h₁ h₂

theorem le_offset_trans₂ {α ω} [Weight ω] [Offset α ω]
    (a b c : α) (k₁ k₂ k₃ k₄ k : ω) :
    k₂ == k₃ + k → offset a k₁ ≤ offset b k₂ → offset b k₃ ≤ offset c k₄ → offset a k₁ ≤ offset c (k₄ + k) := by
  intro h h₁ h₂; simp at h; subst k₂
  replace h₂ := add_le_add' k h₂
  exact Std.le_trans h₁ h₂

theorem lt_offset_trans₁ {α ω} [Weight ω] [Offset α ω]
    (a b c : α) (k₁ k₂ k₃ k₄ k : ω) :
    k₃ == k₂ + k → offset a k₁ < offset b k₂ → offset b k₃ < offset c k₄ → offset a (k₁ + k) < offset c k₄ := by
  intro h h₁ h₂; simp at h; subst k₃
  replace h₁ := add_lt_add' k h₁
  exact Preorder.lt_trans h₁ h₂

theorem lt_offset_trans₂ {α ω} [Weight ω] [Offset α ω]
    (a b c : α) (k₁ k₂ k₃ k₄ k : ω) :
    k₂ == k₃ + k → offset a k₁ < offset b k₂ → offset b k₃ < offset c k₄ → offset a k₁ < offset c (k₄ + k) := by
  intro h h₁ h₂; simp at h; subst k₂
  replace h₂ := add_lt_add' k h₂
  exact Preorder.lt_trans h₁ h₂

theorem le_lt_offset_trans₁ {α ω} [Weight ω] [Offset α ω]
    (a b c : α) (k₁ k₂ k₃ k₄ k : ω) :
    k₃ == k₂ + k → offset a k₁ ≤ offset b k₂ → offset b k₃ < offset c k₄ → offset a (k₁ + k) < offset c k₄ := by
  intro h h₁ h₂; simp at h; subst k₃
  replace h₁ := add_le_add' k h₁
  exact Preorder.lt_of_le_of_lt h₁ h₂

theorem le_lt_offset_trans₂ {α ω} [Weight ω] [Offset α ω]
    (a b c : α) (k₁ k₂ k₃ k₄ k : ω) :
    k₂ == k₃ + k → offset a k₁ ≤ offset b k₂ → offset b k₃ < offset c k₄ → offset a k₁ < offset c (k₄ + k) := by
  intro h h₁ h₂; simp at h; subst k₂
  replace h₂ := add_lt_add' k h₂
  exact Preorder.lt_of_le_of_lt h₁ h₂

theorem lt_le_offset_trans₁ {α ω} [Weight ω] [Offset α ω]
    (a b c : α) (k₁ k₂ k₃ k₄ k : ω) :
    k₃ == k₂ + k → offset a k₁ < offset b k₂ → offset b k₃ ≤ offset c k₄ → offset a (k₁ + k) < offset c k₄ := by
  intro h h₁ h₂; simp at h; subst k₃
  replace h₁ := add_lt_add' k h₁
  exact Preorder.lt_of_lt_of_le h₁ h₂

theorem lt_le_offset_trans₂ {α ω} [Weight ω] [Offset α ω]
    (a b c : α) (k₁ k₂ k₃ k₄ k : ω) :
    k₂ == k₃ + k → offset a k₁ < offset b k₂ → offset b k₃ ≤ offset c k₄ → offset a k₁ < offset c (k₄ + k) := by
  intro h h₁ h₂; simp at h; subst k₂
  replace h₂ := add_le_add' k h₂
  exact Preorder.lt_of_lt_of_le h₁ h₂

/-!
Unsat theorems
-/
attribute [local instance] Weight.decLe Weight.decLt

theorem le_unsat {α ω} [Weight ω] [Offset α ω]
    (a : α) (k₁ k₂ : ω) : offset a k₁ ≤ offset a k₂ → (k₁ ≤ k₂) == false → False := by
  simp; apply weight_le

theorem lt_unsat {α ω} [Weight ω] [Offset α ω]
    (a : α) (k₁ k₂ : ω) : offset a k₁ < offset a k₂ → (k₁ < k₂) == false → False := by
  simp; apply weight_lt

/-!
`Int` internalization theorems
-/

-- **Note**: We use `cutsat` normalizer to "rewrite" `Int` inequalities before converting into offsets.

theorem Int.le (x y k : Int) : x + -1*y + k ≤ 0 ↔ offset x k ≤ offset y (0:Int) := by
  simp [offset]; omega

theorem Int.eq (x y k : Int) : x + -1*y + k = 0 ↔ offset x k = offset y (0:Int) := by
  simp [offset]; omega

/-!
`Nat` internalization theorems
-/

-- **Note**: We use the `Nat` normalizer to "rewrite" `Nat` inequalities before converting into offsets.

theorem Nat.le (x y k₁ k₂ : Nat) : x + k₁ ≤ y + k₂ ↔ offset x k₁ ≤ offset y k₂ := by
  simp [offset]

theorem Nat.eq (x y k₁ k₂ : Nat) : x + k₁ = y + k₂ ↔ offset x k₁ = offset y k₂ := by
  simp [offset]

/-!
Types without `Offset` internalization theorems
-/
attribute [local instance] dummyOffset in
theorem Dummy.le {α : Type u} [LE α] [LT α] [Std.IsPreorder α] [Std.LawfulOrderLT α] (x y : α) : x ≤ y ↔ offset x () ≤ offset y () := by
  simp [offset]

attribute [local instance] dummyOffset in
theorem Dummy.lt {α : Type u} [LE α] [LT α] [Std.IsPreorder α] [Std.LawfulOrderLT α] (x y : α) : x < y ↔ offset x () < offset y () := by
  simp [offset]

attribute [local instance] dummyOffset' in
theorem Dummy'.le {α : Type u} [LE α] [Std.IsPreorder α] (x y : α) : x ≤ y ↔ offset x () ≤ offset y () := by
  simp [offset]

attribute [local instance] dummyOffset' in
theorem Dummy'.lt {α : Type u} [LE α] [Std.IsPreorder α] (x y : α) : x < y ↔ offset x () < offset y () := by
  simp [offset]

/-!
Ring internalization theorems
-/
section

private theorem eq_move {α} [Ring α] (x y : α) : x + -1*y = 0 ↔ x = y := by
  constructor
  next =>
    intro h
    replace h := congrArg (· + y) h; simp at h
    rw [Semiring.add_assoc, ← Ring.neg_eq_neg_one_mul, Ring.neg_add_cancel,
        Semiring.add_zero, Semiring.add_comm, Semiring.add_zero] at h
    assumption
  next => intro h; subst x; rw [← Ring.neg_eq_neg_one_mul, Semiring.add_comm, Ring.neg_add_cancel]

variable {α} [Ring α] [instLe : LE α] [LT α] [instOrdLt : Std.LawfulOrderLT α] [Std.IsPreorder α] [OrderedRing α]
attribute [local instance] Ring.intCast Semiring.natCast

-- **Note**: We use `ring` normalizer to "rewrite" ring inequalities before converting into offsets.

omit instOrdLt in
private theorem le_move (x y : α) : x + -1*y ≤ 0 ↔ x ≤ y := by
  rw [← OrderedAdd.neg_nonneg_iff];
  rw [Semiring.add_comm, Ring.neg_eq_neg_one_mul, Semiring.left_distrib]
  simp [← Ring.neg_eq_neg_one_mul, AddCommGroup.neg_neg]
  rw [← Ring.sub_eq_add_neg, OrderedAdd.sub_nonneg_iff]

private theorem lt_move (x y : α) : x + -1*y < 0 ↔ x < y := by
  rw [← OrderedAdd.neg_pos_iff];
  rw [Semiring.add_comm, Ring.neg_eq_neg_one_mul, Semiring.left_distrib]
  simp [← Ring.neg_eq_neg_one_mul, AddCommGroup.neg_neg]
  rw [← Ring.sub_eq_add_neg, OrderedAdd.sub_pos_iff]

theorem Ring.le (x y : α) (k : Int) : x + -1*y + k ≤ 0 ↔ offset x k ≤ offset y (0:Int) := by
  simp [offset, Ring.intCast_zero, Semiring.add_zero]
  rw [Semiring.add_assoc, Semiring.add_comm (-1*y), ← Semiring.add_assoc, le_move]

theorem Ring.lt (x y : α) (k : Int) : x + -1*y + k < 0 ↔ offset x k < offset y (0:Int) := by
  simp [offset, Ring.intCast_zero, Semiring.add_zero]
  rw [Semiring.add_assoc, Semiring.add_comm (-1*y), ← Semiring.add_assoc, lt_move]

theorem Ring.eq (x y : α) (k : Int) : x + -1*y + k = 0 ↔ offset x k = offset y (0:Int) := by
  simp [offset, Ring.intCast_zero, Semiring.add_zero]
  rw [Semiring.add_assoc, Semiring.add_comm (-1*y), ← Semiring.add_assoc, eq_move]

end

end Offset
end Lean.Grind.Order
