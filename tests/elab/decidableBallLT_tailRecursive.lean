/-!
Regression test for the bounded-quantifier decision procedures `Nat.decidableBallLT`,
`Nat.decidableExistsLT`, and `Nat.decidableExistsLT'`.

These instances run the tail-recursive loops `Nat.allLTTR` and `Nat.anyLTTR`, in compiled code and
in kernel reduction alike. They used to recurse to depth `n` in non-tail position: compiled
`decidableBallLT` rebuilt the predicate at every level, which took *quadratic* time, and kernel
`by decide` kept that structural definition, so it was quadratic for `∀` and hit `maxRecDepth` for
`∃` at `n = 3000`.
-/

-- Compiled path: `decidableBallLT` (bounded `∀` over `Nat`) is linear.
def checkBallLT : Bool := decide (∀ k, k < 2000000 → 0 ≤ k)
/-- info: true -/
#guard_msgs in #eval checkBallLT

-- `decidableForallFin → decidableBallLT` (`∀` over `Fin`).
def checkForallFin : Bool := decide (∀ i : Fin 2000000, 0 ≤ i.val)
/-- info: true -/
#guard_msgs in #eval checkForallFin

-- Correctness of the `∃` instances (`decidableExistsLT`, `decidableExistsFin`,
-- `decidableExistsLT'`); small `n` keeps this fast.
/-- info: true -/
#guard_msgs in #eval decide (∃ k, k < 1000 ∧ k + 1 = 1000)
/-- info: false -/
#guard_msgs in #eval decide (∃ i : Fin 1000, i.val + 1 = 0)
/-- info: true -/
#guard_msgs in #eval decide (∃ k, ∃ _ : k < 1000, k + 1 = 1000)

-- Kernel path: `by decide` proves the same goals.
example : ∀ i : Fin 3, i.val < 3 := by decide
example : ∃ i : Fin 3, i.val = 2 := by decide
example : ¬ ∃ k, k < 4 ∧ k + 1 = 0 := by decide
example : ∀ i, i ≤ 5 → i < 6 := by decide

-- Kernel path at `n = 3000`: the structural instances took ~10 s for `∀` and exceeded
-- `maxRecDepth` (even at 10000) for both `∃` forms. The loops recurse to depth `n` in `whnf`,
-- so `maxRecDepth` is still raised past its default of 512.
set_option maxRecDepth 10000 in
example : ∀ i, i < 3000 → i + 0 = i := by decide
set_option maxRecDepth 10000 in
example : ∃ k, k < 3000 ∧ k + 1 = 3000 := by decide
set_option maxRecDepth 10000 in
example : ∃ k, ∃ _ : k < 3000, k + 1 = 3000 := by decide

-- `by decide` proofs through these instances depend on no axioms.
theorem ball_axioms : ∀ i, i < 8 → 0 ≤ i := by decide
/-- info: 'ball_axioms' does not depend on any axioms -/
#guard_msgs in #print axioms ball_axioms

theorem fin_axioms : ∀ i : Fin 8, 0 ≤ i.val := by decide
/-- info: 'fin_axioms' does not depend on any axioms -/
#guard_msgs in #print axioms fin_axioms

theorem ex_axioms : ∃ m, m < 8 ∧ m + 1 = 4 := by decide
/-- info: 'ex_axioms' does not depend on any axioms -/
#guard_msgs in #print axioms ex_axioms

theorem ex'_axioms : ∃ m, ∃ _ : m < 8, m + 1 = 4 := by decide
/-- info: 'ex'_axioms' does not depend on any axioms -/
#guard_msgs in #print axioms ex'_axioms
