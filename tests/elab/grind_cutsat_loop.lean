/-!
Tests for divisibility constraints with divisor `0` in `grind`'s cutsat procedure.
Cutsat used to store `0 ∣ p` constraints, but the model search assumes a nonzero
divisor: it could loop forever in `DvdSolution.geAvoiding` (the original example
below), or weaken bounds via `tightUsingDvd` and miss refutations. `0 ∣ p` is now
converted into the equality `p = 0` when asserted.
-/

-- Used to hang: `0 ∣ b` with `b ≠ 0` excludes the single solution of the
-- divisibility constraint, and the model search looped bumping the candidate.
theorem mwe {b : Nat} (p : Nat) (x1 x2 : Nat) (hb0 : b ≠ 0) (hab : 0 ∣ b) :
    0 / p ^ x1 ∣ b / p ^ x2 := by
  grind

-- Used to fail: the diseq was folded into the bound `b ≥ 1`, which `tightUsingDvd`
-- then weakened back to `b ≥ 0` using the `0 ∣ b` constraint, producing the bogus
-- model `b := 0`.
example (b : Nat) (h1 : b ≠ 0) (h2 : 0 ∣ b) : False := by
  grind

example (a b : Nat) (h : 0 ∣ a + b) (h1 : a + b ≠ 0) : False := by
  grind
