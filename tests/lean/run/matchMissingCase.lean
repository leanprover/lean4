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

-- set_option trace.Meta.Match.match true

/--
error: Missing cases:
Enum.d, false
Enum.c, false
-/
#guard_msgs(pass trace, all) in
def test2 : Enum → Bool → Nat
  | .a, _ => 0
  | .b, _ => 0
  | _, true => 0
