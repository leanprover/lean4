/--
info: Try this:
  termination_by xs.length / 2 - i
-/
#guard_msgs in
def foo (xs : String) (i : Nat) (a b : String.Iterator) : Bool :=
  if xs.length / 2 ≤ i then
    true
  else if a.curr ≠ b.curr then
    false
  else
    foo xs (i + 1) a.next b.prev
termination_by?

/--
info: Try this:
  termination_by xs.length / 2 - i
-/
#guard_msgs in
def bar (xs : String) (i : Nat) (a b : String.Iterator) : Bool :=
  if i < xs.length / 2 then
    if a.curr ≠ b.curr then
      false
    else
      bar xs (i + 1) a.next b.prev
  else
    true
termination_by?


/--
info: Try this:
  termination_by xs.length / 2 - i
-/
#guard_msgs in
def baz (xs : String) (i : Nat) (a b : String.Iterator) : Bool :=
  if ¬ (i < xs.length / 2) then
    true
  else
    if a.curr ≠ b.curr then
      false
    else
      baz xs (i + 1) a.next b.prev
termination_by?
