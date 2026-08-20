import Std.WP
import Std.Tactic.Do

/-!
`vcgen` succeeds on a goal whose local context is inconsistent. Grind internalizes the
hypotheses during initialization and derives `False`, so no goal reaches the `vcgen` step.
-/

open Std.WP

set_option mvcgen.warning false

-- Baseline without the contradictory hypothesis.
example : ⦃ True ⦄ (pure 3 : Id Nat) ⦃ r, r = 3 ⦄ := by
  vcgen

example (h : false = true) : ⦃ True ⦄ (pure 3 : Id Nat) ⦃ r, r = 3 ⦄ := by
  vcgen

example (h : False) : ⦃ True ⦄ (pure 3 : Id Nat) ⦃ r, r = 3 ⦄ := by
  vcgen

-- The `with` clause keeps internalization on; the discharge step is skipped as well.
example (h : false = true) : ⦃ True ⦄ (pure 3 : Id Nat) ⦃ r, r = 3 ⦄ := by
  vcgen with finish
