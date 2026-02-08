/-!
# Tests for grind with CommSemiring

These tests verify that grind properly propagates `0 * a = 0` and `a * 0 = 0`
for CommSemiring types, not just Semiring types.

See: https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Grind.20failure.20for.20CommSemiring.2C.20not.20Semiring
-/

-- Basic test with Semiring
example {R : Type} [Lean.Grind.Semiring R] (f r : R) (hg : f * r ≠ 0) :
    f ≠ 0 := by
  grind

-- Same test should also work with CommSemiring
example {R : Type} [Lean.Grind.CommSemiring R] (f r : R) (hg : f * r ≠ 0) :
    f ≠ 0 := by
  grind

-- Symmetric case: r * f ≠ 0 implies f ≠ 0
example {R : Type} [Lean.Grind.CommSemiring R] (f r : R) (hg : r * f ≠ 0) :
    f ≠ 0 := by
  grind

-- Both factors must be nonzero
example {R : Type} [Lean.Grind.CommSemiring R] (f r : R) (hg : f * r ≠ 0) :
    f ≠ 0 ∧ r ≠ 0 := by
  grind

-- mul_one and one_mul propagation
example {R : Type} [Lean.Grind.CommSemiring R] (f g : R) (h1 : 1 * f = g) (h2 : g ≠ f) : False := by
  grind

example {R : Type} [Lean.Grind.CommSemiring R] (f g : R) (h1 : f * 1 = g) (h2 : g ≠ f) : False := by
  grind
