import Lean
/-!
Tests that `Meta.isProofQuick` gives a definite answer for applications whose type is a
`motive` bound in the function type, such as `match` auxiliary functions, `casesOn`, `brecOn`,
and recursors.
-/
open Lean Meta Elab Term

universe u

def f : Nat → Nat
  | 0 => 1
  | n+1 => n

elab "#is_proof_quick " t:term : command => Command.liftTermElabM do
  let e ← elabTermAndSynthesize t none
  let e ← instantiateMVars e
  logInfo m!"{toString (← isProofQuick e)}"

/-- info: false -/
#guard_msgs in
#is_proof_quick fun x : Nat => f.match_1 (motive := fun _ => Nat) x (fun _ => 1) (fun n => n)

/-- info: true -/
#guard_msgs in
#is_proof_quick fun x : Nat => f.match_1 (motive := fun _ => True) x (fun _ => trivial) (fun _ => trivial)

/-- info: false -/
#guard_msgs in
#is_proof_quick fun x : Nat => Nat.casesOn (motive := fun _ => Nat) x 1 (fun n => n)

/-- info: true -/
#guard_msgs in
#is_proof_quick fun x : Nat => Nat.rec (motive := fun _ => True) trivial (fun _ _ => trivial) x

/-- info: undef -/
#guard_msgs in
#is_proof_quick fun (motive : Nat → Sort u) (z : motive 0) (s : ∀ n, motive n → motive (n+1)) (x : Nat) =>
  Nat.rec (motive := motive) z s x

/-- info: false -/
#guard_msgs in
#is_proof_quick (1 : Nat) + 1
