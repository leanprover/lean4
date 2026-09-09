import Std.Data.ExtDHashMap
open Std

/-!
Regression test: `ExtDHashMap.contains_empty`, `ExtDHashMap.not_mem_empty` and
`ExtDHashMap.singleton_eq_insert` used to be stated about `DHashMap` instead of
`ExtDHashMap`, so `simp` could not close these goals.
-/

example [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {β : α → Type} {a : α} :
    (∅ : ExtDHashMap α β).contains a = false := by simp

example [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {β : α → Type} {a : α} :
    ¬ a ∈ (∅ : ExtDHashMap α β) := by simp

example [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {β : α → Type} {p : (a : α) × β a} :
    ({p} : ExtDHashMap α β) = (∅ : ExtDHashMap α β).insert p.1 p.2 := by simp
