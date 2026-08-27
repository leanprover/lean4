set_option backward.do.legacy false

-- #3126
/-- error: Unknown identifier `IAmIgnored` -/
#guard_msgs in
example : IO Unit := do
  let x : IAmIgnored ← do pure 1
  return

-- #2676
example : IO Unit := do
  let x ← return

-- #2663
example : Id Unit := do
  let mut x ← if true then pure true else pure false
  if let .true := x then
    x := false

-- #5607
example : Id Unit := do
  let mut val : Bool ← do
    pure true
  val := Bool.not val
  return ()

-- #6426
example (arr : Array Nat) : Unit := Id.run do
  let mut abc := 0
  if 0 = 0 then
    ()
  for (i, j) in [(0, 0)] do
    let a : Nat := i + 2
    if h : arr.size ≤ 4 then
      continue
    else if h : arr[4] ≤ a then
      continue
    else
      if 0 = 0 then
        continue
      abc := 0

-- #9037
def test9037 (x : Option Nat) : Nat := Id.run do
  let mut i ←
    match x with
    | .some v =>
      pure v
    | none =>
      pure 0
  i := i + 1
  return i

-- #8119
/--
error: Type mismatch
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  Type u
of sort `Type (u + 1)`
-/
#guard_msgs in
def test8119.{u, v} {m : Type u → Type v} [Monad m] : m PUnit.{u + 1} := do
  let mut i : Nat := 0
  while true do i := i + 1
