import Std.Data.HashMap
import Std.Data.DHashMap

set_option grind.warning false

open Std

variable [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α ]

example : (∅ : DHashMap α β).isEmpty := by grind
example (m : DHashMap α β) (h : m = ∅): m.isEmpty := by grind

example : (((∅ : HashMap Nat Nat).insert 3 6).insert 4 7).contains 3 := by grind

example : (((∅ : HashMap Nat Nat).insert 3 6).insert 4 7).contains 9 == false := by grind

example (m : HashMap Nat Nat) (h : m.contains 3) : (m.erase 2).contains 3 := by grind
example (m : HashMap Nat Nat) (h : (m.erase 2).contains 3) : m.contains 3 := by grind
example (m : HashMap Nat Nat) : (m.erase 3).contains 3 = false := by grind
example (m : HashMap Nat Nat) (h : m.contains 3 = false) : (m.erase 2).contains 3 = false := by grind

-- A grind bug!
-- example (m : HashMap Nat Nat) : ((m.insert 1 2).insert 3 4).size ≤ m.size := by grind

-- Do we want this?
example (m : HashMap Nat Nat) (h : m.isEmpty) : m[3]? = none := by grind [HashMap.getElem?_of_isEmpty]

example : (((∅ : HashMap Nat Nat).insert 3 6).erase 4)[3]? = some 6 := by
  grind
