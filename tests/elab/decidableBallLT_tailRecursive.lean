/-!
Regression test for the tail-recursive runtime replacements of `Nat.decidableBallLT`,
`Nat.decidableExistsLT`, and `Nat.decidableExistsLT'` (leanprover/lean4#PRNUM).

Before that change these instances recursed to depth `n` in non-tail position. The `def`s below
force the decision procedure to be compiled and run: previously `decidableBallLT` rebuilt the
predicate at every level, so `#eval checkBallLT` took *quadratic* time and did not finish here;
it now returns immediately. (`decidableExists{LT,LT'}` additionally overflowed the stack, but only
for much larger `n` than is fast to evaluate, so those are exercised for correctness only below.)
-/

-- `decidableBallLT` (bounded `∀` over `Nat`): quadratic before, linear now.
def checkBallLT : Bool := decide (∀ k, k < 2000000 → 0 ≤ k)
/-- info: true -/
#guard_msgs in #eval checkBallLT

-- `decidableForallFin → decidableBallLT` (`∀` over `Fin`): quadratic before, linear now.
def checkForallFin : Bool := decide (∀ i : Fin 2000000, 0 ≤ i.val)
/-- info: true -/
#guard_msgs in #eval checkForallFin

-- Correctness of the `∃` replacements (`decidableExistsLT`, `decidableExistsFin`,
-- `decidableExistsLT'`); small `n` keeps this fast.
/-- info: true -/
#guard_msgs in #eval decide (∃ k, k < 1000 ∧ k + 1 = 1000)
/-- info: false -/
#guard_msgs in #eval decide (∃ i : Fin 1000, i.val + 1 = 0)
/-- info: true -/
#guard_msgs in #eval decide (∃ k, ∃ _ : k < 1000, k + 1 = 1000)

-- Kernel `by decide` (small) is unaffected: it still uses the original structural instances.
example : ∀ i : Fin 3, i.val < 3 := by decide
example : ∃ i : Fin 3, i.val = 2 := by decide
example : ¬ ∃ k, k < 4 ∧ k + 1 = 0 := by decide
