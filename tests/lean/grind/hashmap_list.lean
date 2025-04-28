import Std.Data.HashMap

reset_grind_attrs%

open Std

attribute [grind →] List.length_pos_of_mem
attribute [grind] HashMap.size_insert

-- Fails with issue:
-- [issue] type error constructing proof for List.length_pos_of_mem
--     when assigning metavariable ?l with
--       m.insert 1 2
--     has type
--       HashMap Nat Nat : Type
--     but is expected to have type
--       List Nat : Type
example (m : HashMap Nat Nat) : ((m.insert 1 2).insert 3 4).size ≤ m.size := by grind
