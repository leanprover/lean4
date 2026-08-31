import Lean.Data.Iterators.Producers.PersistentHashMap
import Std.Data.Iterators

open Lean

section Empty

/-- info: [] -/
#guard_msgs in
#eval (PersistentHashMap.empty : PersistentHashMap Nat Nat).iter.toList

/-- info: #[] -/
#guard_msgs in
#eval (PersistentHashMap.empty : PersistentHashMap Nat Nat).iter.toArray

end Empty

section Singleton

/-- info: [(1, 10)] -/
#guard_msgs in
#eval do
  let m := (PersistentHashMap.empty : PersistentHashMap Nat Nat).insert 1 10
  return m.iter.toList

end Singleton

section MultipleEntries

-- Iteration order is unspecified, so we sort by key.
/-- info: [(1, 10), (2, 20), (3, 30)] -/
#guard_msgs in
#eval do
  let m := ((PersistentHashMap.empty : PersistentHashMap Nat Nat).insert 1 10).insert 2 20 |>.insert 3 30
  return m.iter.toList.toArray.qsort (·.1 < ·.1) |>.toList

end MultipleEntries

section LargerMap

-- Test with enough entries to exercise the trie structure (branching factor is 32).
/-- info: true -/
#guard_msgs in
#eval Id.run do
  let mut m : PersistentHashMap Nat Nat := PersistentHashMap.empty
  for i in *...(100 : Nat) do
    m := m.insert i (i * 100)
  let result := m.iter.toList.toArray.qsort (·.1 < ·.1) |>.toList
  return result == (List.range 100).map (fun i => (i, i * 100))

end LargerMap

section ForLoop

/-- info: 60 -/
#guard_msgs in
#eval Id.run do
  let m := ((PersistentHashMap.empty : PersistentHashMap Nat Nat).insert 1 10).insert 2 20 |>.insert 3 30
  let mut sum := 0
  for (_, v) in m.iter do
    sum := sum + v
  return sum

end ForLoop

section StringKeys

/-- info: [("a", 1), ("b", 2), ("c", 3)] -/
#guard_msgs in
#eval do
  let m := ((PersistentHashMap.empty : PersistentHashMap String Nat).insert "a" 1).insert "b" 2 |>.insert "c" 3
  return m.iter.toList.toArray.qsort (·.1 < ·.1) |>.toList

end StringKeys

section Overwrite

-- Inserting the same key twice should give the latest value.
/-- info: [(1, 99)] -/
#guard_msgs in
#eval do
  let m := ((PersistentHashMap.empty : PersistentHashMap Nat Nat).insert 1 10).insert 1 99
  return m.iter.toList

end Overwrite

section Count

/-- info: 100 -/
#guard_msgs in
#eval Id.run do
  let mut m : PersistentHashMap Nat Nat := PersistentHashMap.empty
  for i in *...(100 : Nat) do
    m := m.insert i i
  return m.iter.toList.length

end Count
