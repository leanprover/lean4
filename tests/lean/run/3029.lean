import Lean.Data.PersistentHashMap
open Lean

example : ((PersistentHashMap.empty : PersistentHashMap Nat Nat)
    |> (·.insert 1 1)
    |> (·.insert 1 1)
    |> (·.size)) = 1 := by native_decide

example : ((PersistentHashMap.empty : PersistentHashMap Nat Nat)
    |> (·.insert 1 1)
    |> (·.insert 2 1)
    |> (·.size)) = 2 := by native_decide

/-- Inserts the pairs (i * n, i * n) for all `i < k`. -/
def insertPairs (k n : Nat) (m : PersistentHashMap Nat Nat) : PersistentHashMap Nat Nat :=
  (List.range k).foldl (init := m) fun m i => m.insert (n * i) (n * i)

/-- Inserts `0, 1, 2, 3, ..., 2^(j-1)`, and then `0, 2, 4, ..., 2^(j-1)`, and so on. -/
def insertPows (j : Nat) (m : PersistentHashMap Nat Nat) : PersistentHashMap Nat Nat :=
  (List.range j).foldl (init := m) fun m i => insertPairs (2^(j-i)) (2^i) m

/-- As for `insertPows`, but backwards. -/
def insertPows' (j : Nat) (m : PersistentHashMap Nat Nat) : PersistentHashMap Nat Nat :=
  (List.range j).reverse.foldl (init := m) fun m i => insertPairs (2^(j-i)) (2^i) m

example : (insertPows 12 (PersistentHashMap.empty : PersistentHashMap Nat Nat)).size = 4096 := by native_decide
example : (insertPows' 12 (PersistentHashMap.empty : PersistentHashMap Nat Nat)).size = 4096 := by native_decide
