import Std.Tactic.Do
import Std
set_option backward.do.legacy false

open Std Do

set_option grind.warning false
set_option mvcgen.warning false

-- Test that `@[mvcgen_witness_type]` works end-to-end.
--
-- In zero-knowledge proofs, a witness is a concrete value the prover privately knows
-- (e.g. a field element), as opposed to an invariant (a predicate maintained across
-- iterations) or a verification condition (a proposition to prove).
--
-- We model this by axiomatizing a circuit-like computation that requires a concrete
-- witness value. The `mvcgen` tactic classifies the witness goal as `witness1` and
-- the constraint as `vc1`.

-- A witness type: a concrete value the prover supplies (not a predicate).
@[mvcgen_witness_type]
structure SquareRootWitness where
  root : Nat

-- An axiomatized circuit that verifies a square root claim.
opaque checkSquareRoot (n : Nat) : Id Bool

-- Spec: given a witness w whose root squares to n, the circuit returns true.
-- When mvcgen applies this spec, `w` becomes a metavariable of witness type,
-- and the precondition `w.root * w.root = n` becomes a verification condition.
@[spec]
axiom checkSquareRoot_spec {n : Nat} (w : SquareRootWitness) :
    Triple (checkSquareRoot n) ⌜w.root * w.root = n⌝ (⇓ r => ⌜r = true⌝)

def verifySquareRoot : Id Bool := do
  checkSquareRoot 9

-- mvcgen produces:
--   witness1 : SquareRootWitness    (concrete value to provide)
--   vc1 : 3 * 3 = 9                 (constraint, auto-solved after witness instantiation)
-- The prover supplies ⟨3⟩ as the witness; the constraint is then trivially true.
theorem verifySquareRoot_correct :
    ⦃⌜True⌝⦄ verifySquareRoot ⦃⇓ r => ⌜r = true⌝⦄ := by
  mvcgen [verifySquareRoot] witnesses
  · ⟨3⟩

-- With -leave, the VC remains for manual discharge.
theorem verifySquareRoot_manual :
    ⦃⌜True⌝⦄ verifySquareRoot ⦃⇓ r => ⌜r = true⌝⦄ := by
  mvcgen -leave [verifySquareRoot] witnesses
  · ⟨3⟩
  with omega

-- Demonstrate that witnesses and invariants can coexist, with witnesses first.

-- A program that first checks a witness and then loops over a list.
def witnessAndLoop (xs : List Nat) : Id Nat := do
  let mut s := 0
  let _ ← checkSquareRoot 9
  for x in xs do
    s := s + x
  pure s

-- Both witnesses (before invariants) in the mvcgen syntax.
theorem witnessAndLoop_correct (xs : List Nat) :
    ⦃⌜True⌝⦄ witnessAndLoop xs ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen [witnessAndLoop] witnesses
  · ⟨3⟩
  invariants
  · ⇓ _ => ⌜True⌝
  with grind
