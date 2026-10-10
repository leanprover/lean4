/-!
Regression test for #15590.

`grind` reported the internal error `ring term has not been internalized`. While internalizing
`a - b`, the ring solver registered it and immediately replayed the disequality `a ≠ b`. The
Rabinowitsch step then built and internalized `(a - b) * (a - b)⁻¹`, which was still being
internalized by an enclosing frame: the core treated it as internalized, but `(a - b)⁻¹` had no
`ENode` yet. The replayed callbacks are now queued and run once internalization is complete.
-/

theorem bug (a b : Rat) (h : a ≠ b) : (a - b) / (a - b) = 1 := by
  grind

example (a b : Rat) (h : a ≠ b) : (a - b) * (a - b)⁻¹ = 1 := by
  grind

example (a b : Rat) (h : a ≠ b) : (a - b) * (1 / (a - b)) = 1 := by
  grind

example (a b c : Rat) (h : a ≠ b) : c * ((a - b) * (a - b)⁻¹) = c := by
  grind

example (a b : Rat) (h : a ≠ b) : (a - b)⁻¹ * (a - b) = 1 := by
  grind

-- Shapes that already worked: the replayed product differs from the one being internalized.
example (a b : Rat) (h : b ≠ a) : (a - b) / (a - b) = 1 := by
  grind

example (a b : Rat) (h : a ≠ b) : (b - a) / (b - a) = 1 := by
  grind

example (a : Rat) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  grind

open Lean.Grind in
example {K : Type} [Field K] (a b : K) (h : a ≠ b) : (a - b) / (a - b) = 1 := by
  grind

open Lean.Grind in
example {K : Type} [Field K] (a b : K) (h : a ≠ b) : (a - b)⁻¹ * (a - b) = 1 := by
  grind

open Lean.Grind in
example {K : Type} [Field K] (a b c : K) (h : a ≠ b) : c * ((a - b) * (a - b)⁻¹) = c := by
  grind
