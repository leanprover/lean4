import Lean

/-!
Rolling back an environment change through `SavedState.restore` drops the type class resolution
cache entries recorded after it, as a different change could later bring the recorded generations
back, and keeps the entries recorded before the rollback point.
-/

open Lean Meta Elab Command

class Foo where
  val : Nat

@[instance_reducible] def a : Foo := ⟨1⟩
@[instance_reducible] def b : Foo := ⟨2⟩

/-- info: a then b -/
#guard_msgs in
run_meta do
  let s ← saveState
  liftCommandElabM <| elabCommand (← `(attribute [instance] a))
  let r₁ ← synthInstance (mkConst ``Foo)
  s.restore
  liftCommandElabM <| elabCommand (← `(attribute [instance] b))
  let r₂ ← synthInstance (mkConst ``Foo)
  logInfo m!"{r₁} then {r₂}"

class Bar where

instance : Bar := ⟨⟩

class Baz where

/--
trace: [Meta.synthInstance.cache] new: Bar
[Meta.synthInstance.cache] cached: Bar
-/
#guard_msgs in
run_meta do
  let cmd ← `(instance : Baz := ⟨⟩)
  withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
    discard <| synthInstance (mkConst ``Bar)
    let s ← saveState
    liftCommandElabM <| elabCommand cmd
    s.restore
    discard <| synthInstance (mkConst ``Bar)
