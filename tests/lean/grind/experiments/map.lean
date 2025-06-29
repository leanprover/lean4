import Std.Data.HashMap
import Std.Data.DHashMap
import Std.Data.ExtHashMap
open Std

-- Do we want this?
grind_pattern HashMap.getElem?_of_isEmpty => m.isEmpty, m[a]?
example (m : HashMap Nat Nat) (h : m.isEmpty) : m[3]? = none := by grind

-- Do this for List etc?
-- attribute [grind] HashMap.getElem?_eq_some_getElem -- Do we do this for list?
-- Don't just use `@[grind]`, instead add two patterns!
-- Seems unnecessary?
grind_pattern HashMap.getElem?_eq_some_getElem => a ∈ m, m[a]?
