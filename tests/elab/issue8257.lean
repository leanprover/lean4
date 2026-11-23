/-!
Regression test for #8257: `termination_by?` finds the measure `xs.length / 2 - i` when the
recursive call is guarded by different forms of the comparison `i < xs.length / 2`.
-/

/--
info: Try this:
  [apply] termination_by xs.length / 2 - i
-/
#guard_msgs in
def foo (xs : String) (i : Nat) (a b : Nat) : Bool :=
  if xs.length / 2 ≤ i then
    true
  else if a ≠ b then
    false
  else
    foo xs (i + 1) (a + 1) (b - 1)
termination_by?

/--
info: Try this:
  [apply] termination_by xs.length / 2 - i
-/
#guard_msgs in
def bar (xs : String) (i : Nat) (a b : Nat) : Bool :=
  if i < xs.length / 2 then
    if a ≠ b then
      false
    else
      bar xs (i + 1) (a + 1) (b - 1)
  else
    true
termination_by?


/--
info: Try this:
  [apply] termination_by xs.length / 2 - i
-/
#guard_msgs in
def baz (xs : String) (i : Nat) (a b : Nat) : Bool :=
  if ¬ (i < xs.length / 2) then
    true
  else
    if a ≠ b then
      false
    else
      baz xs (i + 1) (a + 1) (b - 1)
termination_by?
