/-!
Regression test for #15525.

`grind ring` propagated `a = b` whenever `k*a` and `k*b` simplified to the same polynomial, without
checking that `a - b` itself simplifies to zero. In `BitVec 2` with `2*x = 0`, both `x` and `x + 2`
reduce to `0` with multiplier `2`, but `x + 2 - x = 2 ≠ 0`. The missing check caused a panic in
`mkImpEqExprProof` and a dummy proof term being sent to the kernel.
-/

-- False statement: `x := 0` gives `2 = 0`, which fails in `BitVec 2`. `grind` used to panic
-- here and produce a bogus proof term.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x : BitVec 2) (h : 2 * x = 0) : x + 2 = x := by
  fail_if_success grind
  sorry

-- True statement: `x + x = 2 * x = 0`, so `hf` gives `f 0`.
example (x : BitVec 2) (f : BitVec 2 → Prop) (h : 2 * x = 0)
    (_ : f (x + 2)) (hf : f (x + x)) : f 0 := by
  grind

example (x : BitVec 2) (h : 2 * x = 0) : x + x = 0 := by
  grind

example (x : BitVec 2) (h : 2 * x = 0) : x + 2 ≠ x := by
  grind
