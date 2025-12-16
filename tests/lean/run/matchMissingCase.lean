inductive Enum where | a | b | c | d

/--
error: Missing cases:
Enum.d
Enum.c
-/
#guard_msgs in
def test : Enum → Nat
  | .a => 0
  | .b => 0

-- TODO: The kernel error below is a regression. No idea where it comes from.

/--
error: Missing cases:
_, false
---
error: (kernel) declaration has metavariables 'test2'
-/
#guard_msgs(pass trace, all) in
def test2 : Enum → Bool → Nat
  | .a, _ => 0
  | .b, _ => 0
  | _, true => 0
