/-!
Checks that deprecated names in projection notation cause just
the name to be marked, not the whole expression.
-/
def Nat.inc (n : Nat) : Nat := n + 1

@[deprecated inc (since := "2025-10-17")]
def Nat.inc' (n : Nat) : Nat := n + 1

/--
@ +2:2...+3:9
warning: `Nat.inc'` has been deprecated: Use `Nat.inc` instead
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  n
  |>.inc'

/--
@ +2:2...11
warning: `Nat.inc'` has been deprecated: Use `Nat.inc` instead
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  n |>.inc'

/--
@ +2:2...10
warning: `Nat.inc'` has been deprecated: Use `Nat.inc` instead
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  (n).inc'

/--
@ +2:2...8
warning: `Nat.inc'` has been deprecated: Use `Nat.inc` instead
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  n.inc'

/--
@ +2:4...8
error: Invalid field `incc`: The environment does not contain `Nat.incc`
  n
has type
  Nat
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  n.incc

/--
@ +2:4...8
error: Invalid field `incc`: The environment does not contain `Nat.incc`
  n
has type
  Nat
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  n.incc.foo
