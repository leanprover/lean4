import Std.Data.HashMap.Lemmas

/-!
Tests for the lemmas about `List.groupByKey` and `Array.groupByKey`: each group is the input
filtered to the elements with that key, in order, and a key is present exactly when some
element has it.
-/

open Std

section
variable {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
  {key : β → α} {k : α}

example (xs : List β) : (xs.groupByKey key).getD k [] = xs.filter (key · == k) :=
  List.getD_groupByKey

example (xs : List β) :
    (xs.groupByKey key)[k]? =
      if xs.any (key · == k) then some (xs.filter (key · == k)) else none :=
  List.getElem?_groupByKey

example (xs : List β) : k ∈ xs.groupByKey key ↔ xs.any (key · == k) :=
  List.mem_groupByKey

example (xs : Array β) : (xs.groupByKey key).getD k #[] = xs.filter (key · == k) :=
  Array.getD_groupByKey

example (xs : Array β) :
    (xs.groupByKey key)[k]? =
      if xs.any (key · == k) then some (xs.filter (key · == k)) else none :=
  Array.getElem?_groupByKey

example (xs : Array β) : k ∈ xs.groupByKey key ↔ xs.any (key · == k) :=
  Array.mem_groupByKey

-- The `getD` and `mem` forms are simp lemmas.
example (xs : List β) : (xs.groupByKey key).getD k [] = xs.filter (key · == k) := by simp
example (xs : List β) : k ∈ xs.groupByKey key ↔ xs.any (key · == k) := by simp
example (xs : Array β) : (xs.groupByKey key).getD k #[] = xs.filter (key · == k) := by simp
example (xs : Array β) : k ∈ xs.groupByKey key ↔ xs.any (key · == k) := by simp

end

-- Concrete groups, as in the docstring examples.
example : ([0, 1, 2, 3, 4, 5, 6].groupByKey (· % 2)).getD 0 [] = [0, 2, 4, 6] := by
  rw [List.getD_groupByKey]; rfl
example : ([0, 1, 2, 3, 4, 5, 6].groupByKey (· % 2)).getD 1 [] = [1, 3, 5] := by
  rw [List.getD_groupByKey]; rfl
example : ([0, 1, 2, 3, 4, 5, 6].groupByKey (· % 2))[2]? = none := by
  rw [List.getElem?_groupByKey]; rfl
example : (#[0, 1, 2, 3, 4, 5, 6].groupByKey (· % 2)).getD 0 #[] = #[0, 2, 4, 6] := by
  rw [Array.getD_groupByKey]; rfl
example : (#[0, 1, 2, 3, 4, 5, 6].groupByKey (· % 2)).getD 1 #[] = #[1, 3, 5] := by
  rw [Array.getD_groupByKey]; rfl
example : 2 ∉ #[0, 1, 2, 3, 4, 5, 6].groupByKey (· % 2) := by
  simp

-- A key that is `==` but not identical to the one used for grouping finds the same group.
example (xs : List Nat) :
    (xs.groupByKey (· % 2)).getD 0 [] = (xs.groupByKey (· % 2)).getD (0 + 0) [] := by
  simp
