/-! The loop annotations elaborate to `vcgen` gadgets that only the new `do` elaborator builds, so
under the legacy elaborator the loops it always had keep working and the annotated forms are
reported as syntax it does not support. -/

set_option backward.do.legacy true

def sum (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for x in xs do
    acc := acc + x
  return acc

/-- info: 6 -/
#guard_msgs in
#eval sum [1, 2, 3]

def countTo (n : Nat) : Id Nat := do
  let mut i := 0
  while i < n do
    i := i + 1
  return i

/-- info: 3 -/
#guard_msgs in
#eval countTo 3

def firstDivisor (n : Nat) : Id Nat := do
  let mut i := 1
  repeat
    i := i + 1
    if n % i = 0 then break
  return i

/-- info: 3 -/
#guard_msgs in
#eval firstDivisor 9

/--
error: unexpected syntax
  do
    let mut acc := 0
    for x in xs
        invariant _pref _suff => 0 ≤ acc do
      acc := acc + x
    return acc
-/
#guard_msgs in
example (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for x in xs invariant _pref _suff => 0 ≤ acc do
    acc := acc + x
  return acc

/--
error: unexpected syntax
  do
    let mut i := 0
    while i < n
        invariant _ => i ≤ n
        decreasing n - i do
      i := i + 1
    return i
-/
#guard_msgs in
example (n : Nat) : Id Nat := do
  let mut i := 0
  while i < n invariant _ => i ≤ n decreasing n - i do
    i := i + 1
  return i

/--
error: unexpected syntax
  do
    let mut i := 0
    repeat
        decreasing n - i
      do
        i := i + 1
    return i
-/
#guard_msgs in
example (n : Nat) : Id Nat := do
  let mut i := 0
  repeat
      decreasing n - i
    do
    i := i + 1
  return i
