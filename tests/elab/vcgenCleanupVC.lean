import Std.WP
import Std.Tactic.Do

/-!
`cleanupVC` head-reduces a verification condition before emitting it, so a loop over a tuple state
states its entry condition as `0 ≤ 0` rather than under a `match` on the state pair, and a
verification condition that reduces to `rfl` never reaches the user.
-/

set_option mvcgen.warning false
set_option warn.sorry false

open Std.WP Lean.Order

/-! ## A tuple state: the `match` on the state pair is reduced away -/

example (xs : List Nat) :
    ⦃ True ⦄ (do
      let mut lo := 0
      let mut hi := 0
      for x in xs invariant _c _s => lo ≤ hi do
        lo := lo + x
        hi := hi + 2 * x
      pure (hi - lo) : Id Nat) ⦃ fun r => r = 0 ⦄ := by
  vcgen
  case vc1 => guard_target =ₛ 0 ≤ 0; exact Nat.le_refl 0
  all_goals sorry

/-! ## A postcondition matching on a constructor: the verification condition closes by `rfl` -/

example (n : Nat) :
    ⦃ True ⦄ (pure (n, n) : Id (Nat × Nat)) ⦃ fun p => match p with | (a, b) => a = b ⦄ := by
  vcgen
