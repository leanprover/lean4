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

/--
error: Missing cases:
_, false
-/
#guard_msgs in
def test2 : Enum → Bool → Nat
  | .a, _ => 0
  | _, true => 0

/--
error: Missing cases:
(some _), false
-/
#guard_msgs in
def test3 : Option Enum → Bool → Nat
  | none, _ => 0
  | some .a, _ => 0
  | some _, true => 0

/--
error: Missing cases:
_, false
-/
#guard_msgs in
def test4 : String → Bool → Nat
  | "a", _ => 0
  | _, true => 0
