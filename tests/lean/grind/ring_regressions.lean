-- These are test cases extracted from Mathlib, where `ring` works but `grind` does not (yet!)

example (n : Nat) :
  1 ^ (n / 3) * 2 ^ t = 2 ^ t := by grind

example (a b : Nat) : 3 * a * b = a * b * 3 := by grind

example (k z : Nat) : k * (z * 2 * (z * 2 + 1)) = z * (k * (2 * (z * 2 + 1))) := by grind

open Lean.Grind

example [Field R] (x : R) (cos : R → R) :
    (cos x ^ 2 + (2 * cos x ^ 2 - 1) ^ 2 + (4 * cos x ^ 3 - 3 * cos x) ^ 2 - 1) / 4 =
      cos x * (cos x ^ 2 - 1 / 2) * (4 * cos x ^ 3 - 3 * cos x) := by
  grind

example [Field R] {sqrtTwo a b c : R} :
    sqrtTwo / 32 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 + (-(a + b + c)) ^ 2) ^ 2 =
      9 * sqrtTwo / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  grind

example [Field R] [LinearOrder R] [Ring.IsOrdered R] (x y z : R) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z ≥ 1) :
    (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) + (y ^ 2 - z * x) / (y ^ 2 + z ^ 2 + x ^ 2) +
      (z ^ 2 - x * y) / (z ^ 2 + x ^ 2 + y ^ 2) =
    1 / 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) := by grind
