import Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

/-!
`vcgen` rewrites the decrease of a `decreasing` measure to a comparison of measure values.
-/

open Std.WP Lean.Order

def countDown (n : Nat) : Id Nat := do
  let mut i := n
  while i > 0
      invariant exit => if exit then i = 0 else True
      decreasing i
    do
    i := i - 1
  return i

theorem countDown_spec (n : Nat) : ⦃⌜True⌝⦄ countDown n ⦃fun r => ⌜r = 0⌝⦄ := by
  vcgen [countDown]
  case vc2 _ _ mb _ _ =>
    guard_target =ₛ i < mb
    grind
  all_goals grind

def countInto : StateM (Nat × Nat) Unit := do
  while (← get).1 < (← get).2
      invariant _exit (lo, hi) => lo ≤ hi
      decreasing (lo, hi) => hi - lo
    do
    modify fun (lo, hi) => (lo + 1, hi)

theorem countInto_spec :
    ⦃fun (lo, hi) => ⌜lo ≤ hi⌝⦄ countInto ⦃fun _ (lo, hi) => ⌜lo ≤ hi⌝⦄ := by
  vcgen [countInto]
  case vc1 _ _ _ _ mb lo hi _ _ =>
    guard_target =ₛ hi - (lo + 1) < mb
    grind
  all_goals grind
