import Std.Async

open Std.Async

/-!
Tests that `for` loops in `Async` and `ContextAsync` over `List`, `Array`, `[a:b]`, `a...b` and
`*...b` run in constant stack space when their steps complete synchronously, including after a step
suspended, and that `break`, `continue`, `return` and `throw` behave as in any other monad whether
steps complete synchronously, have already finished, or suspend.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

@[noinline] def syncStep (acc i : Nat) : Async Nat := pure (acc + i)

/-- A step that suspends on a task that has not finished yet. -/
def pendingStep (acc i : Nat) : Async Nat := do
  let t ← IO.asTask (do IO.sleep 1; pure (acc + i))
  Async.ofAsyncTask t

/-- A step on a task that has already finished. -/
@[noinline] def finishedStep (acc i : Nat) : Async Nat := do
  Async.ofAsyncTask (Task.pure (.ok (acc + i)))

def deep : Nat := 1000000

def sumTo (n : Nat) : Nat := n * (n - 1) / 2

-- Long loops whose steps complete synchronously: the generic instances nest one bind per element.
#eval show IO Unit from do
  let r ← Async.block do
    let mut acc := 0
    for i in [0:deep] do acc ← syncStep acc i
    return acc
  check (r == sumTo deep) s!"[0:n]: {r}"
  let r ← Async.block do
    let mut acc := 0
    for i in 0...deep do acc ← syncStep acc i
    return acc
  check (r == sumTo deep) s!"a...b: {r}"
  let r ← Async.block do
    let mut acc := 0
    for i in *...deep do acc ← syncStep acc i
    return acc
  check (r == sumTo deep) s!"*...b: {r}"
  let xs := Array.range deep
  let r ← Async.block do
    let mut acc := 0
    for i in xs do acc ← syncStep acc i
    return acc
  check (r == sumTo deep) s!"Array: {r}"
  let ys := List.range deep
  let r ← Async.block do
    let mut acc := 0
    for i in ys do acc ← syncStep acc i
    return acc
  check (r == sumTo deep) s!"List: {r}"
  let r ← Async.block <| ContextAsync.run do
    let mut acc := 0
    for i in xs do acc ← syncStep acc i
    return acc
  check (r == sumTo deep) s!"ContextAsync Array: {r}"
  let r ← Async.block <| ContextAsync.run do
    let mut acc := 0
    for i in [0:deep] do acc ← syncStep acc i
    return acc
  check (r == sumTo deep) s!"ContextAsync [0:n]: {r}"

-- After a step suspends, the rest of the loop still runs in constant stack space.
#eval show IO Unit from do
  let r ← Async.block do
    let mut acc := 0
    for i in [0:deep] do
      acc ← if i == 1 then pendingStep acc i else syncStep acc i
    return acc
  check (r == sumTo deep) s!"pending then sync: {r}"

/-- Runs the same loop body with `step`, exercising `continue`, `break` and the loop's result. -/
def controlArray (step : Nat → Nat → Async Nat) : Async Nat := do
  let mut acc := 0
  for i in #[1, 2, 3, 4, 5, 6, 7, 8] do
    if i % 2 == 0 then continue
    if i > 6 then break
    acc ← step acc i
  return acc

def controlRange (step : Nat → Nat → Async Nat) : Async Nat := do
  let mut acc := 0
  for i in 1...9 do
    if i % 2 == 0 then continue
    if i > 6 then break
    acc ← step acc i
  return acc

def earlyReturn (step : Nat → Nat → Async Nat) : Async Nat := do
  let mut acc := 0
  for i in [1, 2, 3, 4] do
    acc ← step acc i
    if acc ≥ 3 then return acc * 100
  return acc

def throwing (step : Nat → Nat → Async Nat) (ran : IO.Ref Nat) : Async Nat := do
  let mut acc := 0
  for i in *...10 do
    acc ← step acc i
    ran.modify (· + 1)
    if i == 3 then throw (IO.userError s!"stop at {acc}")
  return acc

#eval show IO Unit from do
  for (name, step) in [("sync", syncStep), ("finished", finishedStep), ("pending", pendingStep)] do
    let r ← Async.block (controlArray step)
    check (r == 1 + 3 + 5) s!"{name}: Array continue/break gave {r}"
    let r ← Async.block (controlRange step)
    check (r == 1 + 3 + 5) s!"{name}: a...b continue/break gave {r}"
    let r ← Async.block (earlyReturn step)
    check (r == 300) s!"{name}: early return gave {r}"
    let ran ← IO.mkRef 0
    match ← (Async.block (throwing step ran)).toBaseIO with
    | .ok r => throw (IO.userError s!"{name}: throw did not stop the loop, gave {r}")
    | .error e =>
      check (toString e == "stop at 6") s!"{name}: wrong error {e}"
      check ((← ran.get) == 4) s!"{name}: {← ran.get} steps ran after the throw"
