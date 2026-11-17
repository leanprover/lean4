import Lean
import Std.Tactic.Do

/-!
`vcgen` simplifies the hypotheses of a goal `∀ xs, h → G` before it introduces them. The proof of
that step passes each simplified hypothesis by `Eq.mp`, so it contains no congruence over `G`.

In `allAgreePtr`, all jumps to the join point pass the same state, so the hypothesis of its right
side goal simplifies to `True`. A congruence such as `arrow_congr_right` over that goal would
repeat the `wp` body of the join point in the proof.
-/

set_option experimental.vcgen true
set_option Elab.async false
open Lean Meta Std.WP

/-- The congruence lemmas of binder domains that the proof of the theorem `n` uses. -/
def telescopeCongrs (n : Name) : MetaM (List Name) := do
  let .thmInfo t ← getConstInfo n | throwError "no theorem {n}"
  let cs := t.value.getUsedConstants
  return [``implies_congr_left, ``implies_congr, ``arrow_congr_right].filter cs.contains

def allAgreePtr (c : Bool) : StateM Nat Unit := do
  if c then modify (· + 1) else modify (· + 1)
  modify (· + 1)

theorem allAgreePtr_spec : ⦃fun s => s = s₀⦄ allAgreePtr c ⦃fun _ s => s = s₀ + 2⦄ := by
  vcgen +jp [allAgreePtr] with finish

/-- info: [] -/
#guard_msgs in
#eval telescopeCongrs ``allAgreePtr_spec
