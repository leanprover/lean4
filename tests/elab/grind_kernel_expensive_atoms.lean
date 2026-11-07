/-!
Proofs produced by `lia`, `grind` and the `Nat` offset simprocs must not make the kernel reduce atoms
such as `(n + 4294967295) % 4294967296`: `Nat.ble` on the `2^32` literals does not terminate in
practice.
-/

/-!
The kernel-reduction denotations of the certificates (`Poly.denote'_k`, `Expr.denote_k`, ...) must
be unfolded before the arithmetic of the terms they are compared with.
`Int.Internal.Linear.le_norm_poly` with a `CommRing.norm_int_k` certificate:
-/

example (x n : Nat) (h : x * x + (n + 4294967295) % 4294967296 ≤ 3)
    (h' : 5 ≤ (n + 4294967295) % 4294967296) : False := by
  lia

/-! `Lean.Grind.Linarith.le_norm` states the hypothesis with `Linarith.Expr.denote_k`. -/

example (x y : Rat) (n : Nat) (h : x + (((n + 4294967295) % 4294967296 : Nat) : Rat) ≤ y)
    (h' : y < x) : False := by
  grind

/-!
The `Nat` offset simprocs must not state results that are only definitionally equal to the
lemma instances when offsets cancel, e.g., `b ≤ c` for `b ≤ c + (1 - 1)`.
-/

example (x n : Nat) (h : x + 1 ≤ (n + 4294967295) % 4294967296 + 1) :
    x ≤ (n + 4294967295) % 4294967296 := by
  simp only [Nat.reduceLeDiff] at h; exact h

example (x n : Nat) (h : x + 1 = (n + 4294967295) % 4294967296 + 1) :
    x = (n + 4294967295) % 4294967296 := by
  simp only [Nat.reduceEqDiff] at h; exact h

example (n : Nat) (h : (n + 4294967295) % 4294967296 + 1 - 1 = 0) :
    (n + 4294967295) % 4294967296 = 0 := by
  simp only [Nat.reduceSubDiff] at h; exact h

example (x n : Nat) (h : x + 1 - ((n + 4294967295) % 4294967296 + 1) = 0) :
    x - (n + 4294967295) % 4294967296 = 0 := by
  simp only [Nat.reduceSubDiff] at h; exact h

example (x n : Nat) (h : x + 1 ≤ (n + 4294967295) % 4294967296 + 1) :
    x ≤ (n + 4294967295) % 4294967296 := by
  lia

/-! Both issues. -/

theorem pow_mod (L b : Nat) (f9 : 2 * 2 ^ (L - 1) ≤ 2 ^ L) (f10 : 2 ^ L ≤ 2 * 2 ^ (L - 1))
    (f12 : b < 2 ^ (L - 1)) (f16 : (2 ^ L - 1 - b) % 2 ^ 32 = 2 ^ L - 1 - b) :
    ((2 ^ L - 1 - b) % 2 ^ 32 + (2 ^ 32 - 1 % 2 ^ 32)) % 2 ^ 32 + 1 ≤ 2 ^ L := by
  lia
