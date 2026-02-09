module
import Std.Data.HashMap
reset_grind_attrs%

open Std

attribute [grind →] List.length_pos_of_mem
attribute [grind] HashMap.size_insert

set_option trace.grind.issues true in
example (m : HashMap Nat Nat) : ((m.insert 1 2).insert 3 4).size ≥ m.size := by
  grind
