set_option linter.deprecated true

/-!
Checks that deprecated names in projection notation cause just
the name to be marked, not the whole expression.
-/
def Nat.inc (n : Nat) : Nat := n + 1

@[deprecated inc (since := "2025-10-17")]
def Nat.inc' (n : Nat) : Nat := n + 1

/--
@ +3:5...9
warning: `Nat.inc'` has been deprecated: Use `Nat.inc` instead
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  n
  |>.inc'

/--
@ +2:7...11
warning: `Nat.inc'` has been deprecated: Use `Nat.inc` instead
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  n |>.inc'

/--
@ +2:6...10
warning: `Nat.inc'` has been deprecated: Use `Nat.inc` instead
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  (n).inc'

/--
@ +2:4...8
warning: `Nat.inc'` has been deprecated: Use `Nat.inc` instead
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  n.inc'

/--
@ +2:4...8
error: Invalid field `incc`: The environment does not contain `Nat.incc`, so it is not possible to project the field `incc` from an expression
  n
of type `Nat`
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  n.incc

/--
@ +2:4...8
error: Invalid field `incc`: The environment does not contain `Nat.incc`, so it is not possible to project the field `incc` from an expression
  n
of type `Nat`
-/
#guard_msgs (positions := true) in
example (n : Nat) : Nat :=
  n.incc.foo
