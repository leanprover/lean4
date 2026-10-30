import Lean

/-!
`debug.synthInstance.checkCacheHits` reports a served type class resolution cache entry that
differs from recomputation with a panic, without otherwise affecting elaboration. The stale entry
comes from rolling back the environment bypassing `Meta.SavedState.restore`, the documented
limitation of `Lean.Meta.SynthInstanceCache`.
-/

open Lean Meta Elab Command

set_option debug.synthInstance.checkCacheHits true

class Foo where
  val : Nat

@[instance_reducible] def a : Foo := ⟨1⟩
@[instance_reducible] def b : Foo := ⟨2⟩

#guard_panic in
/-- info: a then a -/
#guard_msgs in
run_meta do
  let s ← (Core.saveState : CoreM _)
  liftCommandElabM <| elabCommand (← `(attribute [instance] a))
  let r₁ ← synthInstance (mkConst ``Foo)
  (s.restore : CoreM Unit)
  liftCommandElabM <| elabCommand (← `(attribute [instance] b))
  let r₂ ← synthInstance (mkConst ``Foo)
  logInfo m!"{r₁} then {r₂}"
