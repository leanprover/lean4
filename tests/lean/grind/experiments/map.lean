import Std.Data.HashMap
import Std.Data.DHashMap
import Std.Data.ExtHashMap
set_option grind.warning false

open Std

-- Do we want this?
example (m : HashMap Nat Nat) (h : m.isEmpty) : m[3]? = none := by grind [HashMap.getElem?_of_isEmpty]

-- Don't just use `@[grind]`, instead add two patterns!
-- Do this for List etc?
-- attribute [grind] HashMap.getElem?_eq_some_getElem -- Do we do this for list?
grind_pattern HashMap.getElem?_eq_some_getElem => a ∈ m, m[a]?

example (m : HashMap Nat Nat) : ((m.alter 5 id).erase 7).size ≥ m.size - 1 := by grind

example (m : ExtHashMap Nat Nat) :
    (m.insert 1 2).filter (fun k v => k > 1000) = (m.insert 1 3).filter fun k v => k > 1000 := by
  ext1 k
  grind

example (m : ExtHashMap Nat Nat) :
    (((m.insert 1 2).insert 3 4).insert 5 6).filter (fun k v => k > 6) = m.filter fun k v => k > 6 := by
  ext1 k
  grind
