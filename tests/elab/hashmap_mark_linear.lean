import Std.Data.HashMap

/-!
Tests that `markLinear` and `propagateMark` on `HashMap` is the identity
-/

open Std

variable {α : Type} {β : Type} [BEq α] [Hashable α]

example (m : HashMap α β) : m.markLinear = m := by simp
example (m : HashMap.Raw α β) : m.markLinear = m := by simp
example (m : DHashMap α (fun _ => β)) : m.markLinear = m := by simp
example (m : DHashMap.Raw α (fun _ => β)) : m.markLinear = m := by simp

example (m : HashMap α β) (a : α) (b : β) : (m.markLinear.insert a b).size = (m.insert a b).size := by
  simp

example (m : HashMap α β) (a : α) : m.markLinear.contains a = m.contains a := by simp

example (m : HashMap α β) : m.markLinear.markLinear = m.markLinear := by simp

example (m : HashMap α β) (a : α) (b : β) :
    (m.insert a b).markLinear = (m.markLinear.insert a b).markLinear := by
  simp

example (m : HashMap.Raw α β) (h : m.WF) : m.markLinear.WF := h.markLinear
example (m : DHashMap.Raw α (fun _ => β)) (h : m.WF) : m.markLinear.WF := h.markLinear
example (m : HashMap α β) : m.markLinear = m := rfl
example (m : DHashMap.Raw α (fun _ => β)) : m.markLinear = m := rfl
