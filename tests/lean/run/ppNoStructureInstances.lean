/-!
# Test for the `pp_no_structure_instances` attribute
-/

structure Opposite (α : Type u) where
  op :: unop : α

/-- info: { unop := 1 } : Opposite Nat -/
#guard_msgs in
#check (Opposite.op 1)

attribute [pp_no_structure_instances] Opposite

/-- info: Opposite.op 1 : Opposite Nat -/
#guard_msgs in
#check (Opposite.op 1)

open Opposite

/-- info: op 1 : Opposite Nat -/
#guard_msgs in
#check (Opposite.op 1)
