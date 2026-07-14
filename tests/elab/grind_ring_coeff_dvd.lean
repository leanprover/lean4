module

/-!
Tests that the `grind` ring solver does not lose basis equations to destructive
pseudo-reduction. Rewriting an equation with a rule whose leading coefficient does not
divide the target coefficient multiplies the equation by a constant `k ≠ ±1`; replacing
the original equation with the result loses information in rings without
`NoNatZeroDivisors`. For example, below, the basis contains `B ^ 2 = 0` and `B * A + 2 = 0`,
superposition derives `2 * B = 0`, and inserting the latter into the basis used to destroy
both original equations (`B ^ 2 = 0` became `0 = 0` and `B * A + 2 = 0` became `4 = 0`),
making the goal, which follows from `H` alone, unprovable.
-/

open Lean.Grind

-- Basis interreduction path (`EqCnstr.simplifyBasis`): `2 * B = 0` is derived by
-- superposition and used to be applied destructively to the rest of the basis.
example {R : Type u} [CommRing R] (A B : R) (H₀ : B ^ 2 = 0) (H : A * B = -2) :
    B + A * B = B - 2 := by
  grind

-- Assertion path (`EqCnstr.simplify`): with `2 * B = 0` already in the basis,
-- `A * B = -2` used to be destroyed while being simplified during assertion.
example {R : Type u} [CommRing R] (A B : R) (H₀ : 2 * B = 0) (H : A * B = -2) :
    B + A * B = B - 2 := by
  grind

-- With `NoNatZeroDivisors` the rewrites are information-preserving and this always worked.
example {R : Type u} [CommRing R] [NoNatZeroDivisors R] (A B : R)
    (H₀ : B ^ 2 = 0) (H : A * B = -2) : B + A * B = B - 2 := by
  grind

-- The consequences of the skipped rewrites must still be derived via superposition:
-- here `4 = 0` follows from the hypotheses, which is absurd in `Int`.
example (A B : Int) (H₀ : B ^ 2 = 0) (H : A * B = -2) : False := by
  grind
