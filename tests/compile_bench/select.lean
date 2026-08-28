import Std.Async.Select

/-!
Benchmarks `Selectable.one` on a pair of custom `Selectable`s that resolve
instantly via their non-blocking `tryFn`, exercising the fast path of the
selection protocol in a configurable iteration loop.
-/

open Std Async

/-- A `Selector` that instantly resolves with `value` through its non-blocking `tryFn`. -/
def instantSelector (value : α) : Selector α where
  tryFn := pure (some value)
  registerFn _ := pure ()
  unregisterFn := pure ()

/-- A `Selectable` built from `instantSelector` that yields `value` unchanged. -/
def instantSelectable (value : Nat) : Selectable Nat :=
  .case (instantSelector value) pure

def bench (iterations : Nat) : Async Nat := do
  let mut acc := 0
  for i in *...iterations do
    acc := acc + (← Selectable.one #[instantSelectable i, instantSelectable (i + 1)])
  return acc

def run (name : String) (iterations : Nat) : IO Unit := do
  let t1 ← IO.monoMsNow
  let acc ← (bench iterations).block
  let t2 ← IO.monoMsNow
  let time : Float := (t2 - t1).toFloat / 1000.0
  IO.println s!"measurement: {name} {time} s"
  -- Consume `acc` so the loop cannot be optimized away; the bound is never hit.
  if acc > iterations * iterations + iterations then
    throw <| .userError "unreachable"

def main (args : List String) : IO Unit := do
  let iterations := args[0]!.toNat!
  run "select_one_two" iterations
