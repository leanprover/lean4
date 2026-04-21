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
