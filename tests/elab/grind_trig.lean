module
axiom R : Type
instance : Lean.Grind.CommRing R := sorry

axiom cos : R → R
axiom sin : R → R
axiom trig_identity : ∀ x, (cos x)^2 + (sin x)^2 = 1

grind_pattern trig_identity => cos x
grind_pattern trig_identity => sin x

-- Whenever `grind` sees `cos` or `sin`, it adds `(cos x)^2 + (sin x)^2 = 1` to the blackboard.
-- That's a polynomial, so it is sent to the Grobner basis module.
-- And we can prove equalities modulo that relation!
example : (cos x + sin x)^2 = 2 * cos x * sin x + 1 := by
  grind

-- `grind` notices that the two arguments of `f` are equal,
-- and hence the function applications are too.
example (f : R → Nat) : f ((cos x + sin x)^2) = f (2 * cos x * sin x + 1) := by
  grind

-- After that, we can use basic modularity conditions:
-- this reduces to `4 * x ≠ 2 + x` for some `x : ℕ`
example (f : R → Nat) : 4 * f ((cos x + sin x)^2) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind

-- A bit of case splitting is also fine.
-- If `max = 3`, then `f _ = 0`, and we're done.
-- Otherwise, the previous argument applies.
example (f : R → Nat) : max 3 (4 * f ((cos x + sin x)^2)) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind

-- See https://github.com/leanprover-community/mathlib4-nightly-testing/blob/nightly-testing/MathlibTest/grind/trig.lean
-- for the Mathlib version of this test, using the real `ℝ`, `cos`, `sin`, and `cos_sq_and_sin_sq` declarations.
