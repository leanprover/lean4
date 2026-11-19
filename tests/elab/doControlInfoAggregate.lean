set_option backward.do.legacy false

-- When an inner doElem's `ControlInfo` has `numRegularExits := 0` (because all branches
-- `break`/`continue`/`return`, or it is a non-terminating `repeat`), the trailing `return`
-- inside the enclosing `for` body used to be dropped during inference, and the for elaborator
-- then threw "Early returning ... but the info said there is no early return" even though the
-- elaborator does visit the trailing element. `ofSeq`/`ControlInfo.sequence` now aggregate
-- `breaks`/`continues`/`returnsEarly`/`reassigns` past `numRegularExits == 0` elements, so the
-- inferred info matches what the elaborator actually sees.

/--
warning: This `do` element and its control-flow region are dead code. Consider refactoring your code to remove it.
-/
#guard_msgs in
example (cond : Bool) : IO Nat := do
  for _ in [1, 2] do
    if cond then break else break
    return 42
  return 1

/--
warning: This `do` element and its control-flow region are dead code. Consider refactoring your code to remove it.
-/
#guard_msgs in
example (cond : Bool) : IO Nat := do
  for _ in [1, 2] do
    if cond then continue else continue
    return 42
  return 1

/--
warning: This `do` element and its control-flow region are dead code. Consider refactoring your code to remove it.
-/
#guard_msgs in
example (i : Nat) : IO Nat := do
  for _ in [1, 2] do
    match i with
    | 0 => break
    | _ => break
    return 42
  return 1

/--
warning: This `do` element and its control-flow region are dead code. Consider refactoring your code to remove it.
-/
#guard_msgs in
example : IO Nat := do
  for _ in [1, 2] do
    try break catch _ => break
    return 42
  return 1

/--
warning: This `do` element and its control-flow region are dead code. Consider refactoring your code to remove it.
-/
#guard_msgs in
example (cond : Bool) : IO Nat := do
  for _ in [1, 2] do
    unless cond do break
    if cond then break else break
    return 42
  return 1

#guard_msgs in
example : IO Nat := do
  for _ in [1, 2] do
    repeat
      pure ()
    return 42
  return 1

-- Neither branch of the `if` can terminate normally, so the dead-code warning fires on
-- `return 2`. The user can act on the warning: removing `return 2` still leaves the do block
-- well-typed because `elabDoRepeat` injects an `unreachable!` into each branch's expansion.
/--
warning: This `do` element and its control-flow region are dead code. Consider refactoring your code to remove it.
-/
#guard_msgs in
example (x : Nat) : Id Nat := do
  if x = 3 then
    repeat
      pure ()
  else
    repeat
      pure ()
  return 2

-- A break-less `repeat` whose body early-returns: `elabDoRepeat` injects an `unreachable!`, so
-- the do block's `Id Nat` result type is recovered from the body's `return`.
#guard_msgs in
example (n : Nat) : Id Nat := do
  let mut i := 0
  repeat
    if i = n then return i
    i := i + 1

-- Break-less, return-less `repeat` inside an action whose result type is polymorphic. The loop
-- body never terminates, so `elabDoRepeat` leaves the expansion as a plain `for _ in Loop.mk`
-- and the inner do block types as `m PUnit`, letting `BaseIO.asTask`'s polymorphic `α` resolve
-- to `PUnit`.
#guard_msgs in
example : BaseIO Unit := do
  let _ ← BaseIO.asTask do
    repeat
      pure ()
