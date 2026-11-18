import Lean
import Std.Tactic.Do

/-!
`vcgen` simplifies the hypotheses of a goal `∀ xs, h → G` before it introduces them. The proof of
that step passes each simplified hypothesis by `Eq.mp`, so it contains no congruence over `G`.

In `pairBranch`, `vcgen` destructures the state into `(a, b)`, so the hypothesis of the `then`
branch reads `(a, b).fst < (a, b).snd` and simplifies to `a < b`. The conclusion `G` of that goal
is the `wp` of the rest of the program, which a congruence such as `arrow_congr_left` would repeat
in the proof.
-/

set_option experimental.vcgen true
set_option Elab.async false
open Lean Meta Std.WP

/-- The congruence lemmas of binder domains that the proof of the theorem `n` uses. -/
def telescopeCongrs (n : Name) : MetaM (List Name) := do
  let .thmInfo t ← getConstInfo n | throwError "no theorem {n}"
  let cs := t.value.getUsedConstants
  return [``implies_congr_left, ``implies_congr, ``arrow_congr_left, ``arrow_congr_right,
    ``arrow_congr].filter cs.contains

def pairBranch : StateM (Nat × Nat) Unit := do
  let s ← get
  if s.1 < s.2 then set (s.1 + 1, s.2) else set (s.1, s.2 + 1)
  modify fun s => (s.1 + 1, s.2)
  modify fun s => (s.1, s.2 + 1)

theorem pairBranch_spec : ⦃fun s => s = s₀⦄ pairBranch ⦃fun _ s => s₀.2 < s.2⦄ := by
  vcgen [pairBranch] with finish

/-- info: [] -/
#guard_msgs in
#eval telescopeCongrs ``pairBranch_spec
