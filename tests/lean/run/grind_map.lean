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

-- Insert twice
example (m : HashMap Nat Nat) : m.size ≤ ((m.insert 1 2).insert 3 4).size := by grind
example (m : HashMap Nat Nat) : ((m.insert 1 2).insert 3 4).size ≤ m.size + 2 := by grind
-- Insert the same key twice
example (m : HashMap Nat Nat) : m.size ≤ ((m.insert 1 2).insert 1 4).size := by grind
example (m : HashMap Nat Nat) : ((m.insert 1 2).insert 1 4).size ≤ m.size + 1 := by grind

attribute [grind] Option.pmap_eq_map

-- This probably should be in the library to begin with.
theorem getElem?_map'
  {m : HashMap α β} {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.map (f k) := by
  grind

-- Do we want this?
example (m : HashMap Nat Nat) (h : m.isEmpty) : m[3]? = none := by grind [HashMap.getElem?_of_isEmpty]

example : (((∅ : HashMap Nat Nat).insert 3 6).erase 4)[3]? = some 6 := by grind

attribute [grind] HashMap.getElem?_eq_some_getElem -- Do we do this for list?

example (m : HashMap Nat Nat) : ((m.alter 5 id).erase 7).size ≥ m.size - 1 := by grind

open scoped HashMap

attribute [grind] Option.pfilter_eq_filter

-- attribute [ext, grind ext] HashMap.Equiv.of_forall_getElem?_eq
attribute [grind] HashMap.Equiv.of_forall_getElem?_eq

example (m : HashMap Nat Nat) :
    (m.insert 1 2).filter (fun k v => k > 1000) ~m m.filter fun k v => k > 1000 := by
  -- apply HashMap.Equiv.of_forall_getElem?_eq
  grind -- Aggressively abstracting proofs means we can't tell when an argument is unused.


example (m : HashMap Nat Nat) :
    (((m.insert 1 2).insert 3 4).insert 5 6).filter (fun k v => k > 6) ~m m.filter fun k v => k > 6 := by
  apply HashMap.Equiv.of_forall_getElem?_eq
  grind (gen := 10)


#exit

* Push the `grind_hashmap_list_issue` branch, and tell Leo about it.
* Push the `grind_getKey_eq` branch, and tell Leo about it.
* Push the branch `findrev` and merge it
* Push the branch `eraseDupsBy` and merge it
