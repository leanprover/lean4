import Lean
import Std.Tactic.Do

/-!
Exercises pure propositional hypotheses in preconditions. `flipp` flips a `Bool` state, but
its specs only apply under a pure precondition fixing the current value (`b = true` / `b = false`),
so VC generation must introduce and discharge these pure preconditions. `step` flips twice,
preserving `b = true`.
-/

open Lean Meta Order Std.Internal.Do

namespace PurePrecond

set_option mvcgen.warning false

def flipp (_ : Bool) : StateM Bool Unit := modify not

@[spec]
theorem Spec.flipp_true :
    ⦃fun b => b = true⦄ (flipp true) ⦃fun _ b => b = false⦄ := by
  simp only [flipp, modify]
  vcgen with finish

@[spec]
theorem Spec.flipp_false :
    ⦃fun b => b = false⦄ (flipp false) ⦃fun _ b => b = true⦄ := by
  simp only [flipp, modify]
  vcgen with finish

def step : StateM Bool Unit := do
  flipp true
  flipp false

def loop (n : Nat) : StateM Bool Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

def Goal (n : Nat) : Prop := ⦃fun b => b = true⦄ loop n ⦃fun _ b => b = true⦄

end PurePrecond
