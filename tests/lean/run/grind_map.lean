import Std.Data.HashMap
import Std.Data.DHashMap
import Std.Data.ExtHashMap
import Std.Data.HashSet
import Std.Data.TreeMap

open Std

section

variable [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α ]

example : (∅ : DHashMap α β).isEmpty := by grind
example (m : DHashMap α β) (h : m = ∅) : m.isEmpty := by grind

example : (((∅ : HashMap Nat Nat).insert 3 6).insert 4 7).contains 3 := by grind

example : (((∅ : HashMap Nat Nat).insert 3 6).insert 4 7).contains 9 == false := by grind

example (m : HashMap Nat Nat) (h : m.contains 3) : (m.erase 2).contains 3 := by grind
example (m : HashMap Nat Nat) (h : (m.erase 2).contains 3) : m.contains 3 := by grind
example (m : HashMap Nat Nat) : (m.erase 3).contains 3 = false := by grind
example (m : HashMap Nat Nat) (h : m.contains 3 = false) : (m.erase 2).contains 3 = false := by grind

-- Insert twice
example (m : HashMap Nat Nat) : m.size ≤ ((m.insert 1 2).insert 3 4).size := by grind
example (m : HashMap Nat Nat) : ((m.insert 1 2).insert 3 4).size ≤ m.size + 2 := by grind
-- Insert the same key twice
example (m : HashMap Nat Nat) : m.size ≤ ((m.insert 1 2).insert 1 4).size := by grind
example (m : HashMap Nat Nat) : ((m.insert 1 2).insert 1 4).size ≤ m.size + 1 := by grind

example : (((∅ : HashMap Nat Nat).insert 3 6).erase 4)[3]? = some 6 := by grind

open scoped HashMap in
example (m : HashMap Nat Nat) :
    (m.insert 1 2).filter (fun k _ => k > 1000) ~m m.filter fun k _ => k > 1000 := by
  apply HashMap.Equiv.of_forall_getElem?_eq
  grind

example [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
  {m : HashMap α β} {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.map (f k) := by
  grind

example (m : Std.TreeMap Nat Bool) : (m.insert 37 true)[32]? = m[32]? := by
  grind

example (m : HashMap Nat Nat) : ((m.alter 5 id).erase 7).size ≥ m.size - 1 := by grind

example (m : ExtHashMap Nat Nat) :
    (m.insert 1 2).filter (fun k _ => k > 1000) = (m.insert 1 3).filter fun k _ => k > 1000 := by
  ext1 k
  grind

example (m : ExtHashMap Nat Nat) :
    (((m.insert 1 2).insert 3 4).insert 5 6).filter (fun k _ => k > 6) = m.filter fun k _ => k > 6 := by
  ext1 k
  grind

end
