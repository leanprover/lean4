import Lean
open Lean Meta

/-!
`simp` on a dependent forall over a `Prop` domain: when simplifying the domain returns a proof
but leaves the term unchanged, `simpForall` must not cast the binder. The cast survives inside
proof arguments the recursive `simp` does not visit, so the result never equals the input and
`simp` loops until `maxRecDepth`.
-/

/-- Reports a change on an application of a local function without changing the term. -/
simproc idProof (_) := fun e => do
  unless e.isApp && e.appFn!.isFVar do return .continue
  return .visit { expr := e, proof? := some (← mkEqRefl e) }

set_option maxRecDepth 512

example (r : Int → Prop) (P : ∀ x : Int, r x → Prop) (x : Int) :
    (∀ (b : r x), P x b) → True := by
  simp only [idProof, implies_true]

-- The `+arith` normalizer reports a change on the already-normal `d + ↑k + -1`.
example (d : Int) (k : Nat) (r : Int → Prop) (P : ∀ x : Int, r x → Prop)
    (h : ∀ (b : r (d + ↑k + -1)), P (d + ↑k + -1) b) :
    ∀ (b : r (↑k + d - 1)), P (↑k + d - 1) b := by
  simpa +arith only using h
