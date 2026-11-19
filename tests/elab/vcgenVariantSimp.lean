import Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

/-!
`vcgen` rewrites the decrease of a `decreasing` measure to a comparison of measure values. It
substitutes the measure value `mb` of the iteration's start state, so that for `decreasing i` the
verification condition is `i - 1 < i`.
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

/--
trace: case vc1
n i : Nat
a✝ :
  have exit := true;
  if exit = true then i = 0 else True
⊢ i = 0

case vc2
n i✝ mb✝ : Nat
a✝ :
  have exit := false;
  if exit = true then i✝ = 0 else True
h✝ : 0 < i✝
i : Nat := i✝ - 1
⊢ i < i✝

case vc3
n i mb✝ : Nat
a✝ :
  have exit := false;
  if exit = true then i = 0 else True
h✝ : ¬0 < i
⊢ i = 0
-/
#guard_msgs in
theorem countDown_spec (n : Nat) : ⦃⌜True⌝⦄ countDown n ⦃fun r => ⌜r = 0⌝⦄ := by
  vcgen [countDown]
  trace_state
  all_goals grind

def countInto : StateM (Nat × Nat) Unit := do
  while (← get).1 < (← get).2
      invariant _exit (lo, hi) => lo ≤ hi
      decreasing (lo, hi) => hi - lo
    do
    modify fun (lo, hi) => (lo + 1, hi)

/--
trace: case vc1
a✝³ b✝² : Nat
a✝² : a✝³ ≤ b✝²
b✝¹ : PUnit
mb✝ a✝¹ b✝ : Nat
a✝ : a✝¹ ≤ b✝
h✝ : a✝¹ < b✝
⊢ b✝ - (a✝¹ + 1) < b✝ - a✝¹

case vc2
a✝³ b✝² : Nat
a✝² : a✝³ ≤ b✝²
b✝¹ : PUnit
mb✝ a✝¹ b✝ : Nat
a✝ : a✝¹ ≤ b✝
h✝ : a✝¹ < b✝
⊢ a✝¹ + 1 ≤ b✝
-/
#guard_msgs in
theorem countInto_spec :
    ⦃fun (lo, hi) => ⌜lo ≤ hi⌝⦄ countInto ⦃fun _ (lo, hi) => ⌜lo ≤ hi⌝⦄ := by
  vcgen [countInto]
  trace_state
  all_goals grind
