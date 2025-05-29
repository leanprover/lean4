import Std.Data.HashMap
import Std.Data.DHashMap
import Std.Data.ExtHashMap
import Std.Data.HashSet
import Std.Data.TreeMap

set_option grind.warning false

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
  grind (gen := 6)

example [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
  {m : HashMap α β} {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.map (f k) := by
  grind

example (m : Std.TreeMap Nat Bool) : (m.insert 37 true)[32]? = m[32]? := by
  grind

end
