import Std.Data.HashSet

/-!
Tests that `markLinear` on `HashSet` and `HashSet.Raw` is the identity, and that this is visible to
`simp`, `grind` and `rfl`.
-/

open Std

variable {α : Type} [BEq α] [Hashable α]

example (s : HashSet α) : s.markLinear = s := by simp
example (s : HashSet.Raw α) : s.markLinear = s := by simp
example (s : HashSet α) : s.markLinear = s := rfl
example (s : HashSet.Raw α) : s.markLinear = s := rfl

example (s : HashSet α) (a : α) : (s.markLinear.insert a).size = (s.insert a).size := by simp

example (s : HashSet α) (a : α) : s.markLinear.contains a = s.contains a := by simp

example (s : HashSet α) (a : α) : s.markLinear.contains a = s.contains a := by grind

example (s : HashSet.Raw α) (a : α) : s.markLinear.contains a = s.contains a := by grind

example (s : HashSet α) (a : α) :
    (s.insert a).markLinear = (s.markLinear.insert a).markLinear := by
  simp

example (s : HashSet.Raw α) (h : s.WF) : s.markLinear.WF := h.markLinear
