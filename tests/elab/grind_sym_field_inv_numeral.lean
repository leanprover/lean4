/-!
For a numeral `k` in a field, `grind`'s ring module asserts `k * k⁻¹ = 1` to relate the atom
`k⁻¹` to `k`. The fact must reach the ring module unnormalized: the `Sym.simp` normalizer knows
the identity and rewrites the fact to `True`, so the ring module never learned how `2⁻¹`
relates to `2` (`grind_field_div` with `backward.grind.normalizer := false`).
-/

set_option backward.grind.normalizer false
open Std Lean Grind

example [Field R] [IsCharP R 0] (f : R → R) (a b : R) (h : f (a * 2⁻¹) = 1) (h2 : a = 2 * b) :
    f b = 1 := by
  grind

example [Field R] [IsCharP R 7] (f : R → R) (a b : R) (h : f (a * 2⁻¹) = 1) (h2 : a = 2 * b) :
    f b = 1 := by
  grind

example [Field R] [IsCharP R 3] (f : R → R) (a : R) (h : f (a * 3⁻¹) = 1) : f 0 = 1 := by
  grind

example [Field R] [IsCharP R 0] (x : R) (cos : R → R) :
    (cos x ^ 2 + (2 * cos x ^ 2 - 1) ^ 2 + (4 * cos x ^ 3 - 3 * cos x) ^ 2 - 1) / 4 =
      cos x * (cos x ^ 2 - 1 / 2) * (4 * cos x ^ 3 - 3 * cos x) := by
  grind

example [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] (x y z : α)
    : x > 0 → y > 0 → z > 0 → x * y * z ≥ 1 →
      (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) + (y ^ 2 - z * x) / (y ^ 2 + z ^ 2 + x ^ 2) +
        (z ^ 2 - x * y) / (z ^ 2 + x ^ 2 + y ^ 2) =
      1 / 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) := by
  grind
