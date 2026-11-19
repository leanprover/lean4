import Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

/-!
`vcgen` rewrites the decrease of a `decreasing` measure to a comparison of measure values. The
lifted precondition yields the hypothesis `mb = i` on the measure value `mb`, which the verification
condition substitutes: for `decreasing i`, the decrease is `i - 1 < i`.
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
a✝¹ : mb✝ = i✝
a✝ :
  have exit := false;
  if exit = true then i✝ = 0 else True
h✝ : 0 < i✝
i : Nat := i✝ - 1
⊢ i < i✝

case vc3
n i mb✝ : Nat
a✝¹ : mb✝ = i
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
a✝⁴ b✝² : Nat
a✝³ : a✝⁴ ≤ b✝²
b✝¹ : PUnit
mb✝ a✝² b✝ : Nat
a✝¹ : mb✝ = b✝ - a✝²
a✝ : a✝² ≤ b✝
h✝ : a✝² < b✝
⊢ b✝ - (a✝² + 1) < b✝ - a✝²

case vc2
a✝⁴ b✝² : Nat
a✝³ : a✝⁴ ≤ b✝²
b✝¹ : PUnit
mb✝ a✝² b✝ : Nat
a✝¹ : mb✝ = b✝ - a✝²
a✝ : a✝² ≤ b✝
h✝ : a✝² < b✝
⊢ a✝² + 1 ≤ b✝
-/
#guard_msgs in
theorem countInto_spec :
    ⦃fun (lo, hi) => ⌜lo ≤ hi⌝⦄ countInto ⦃fun _ (lo, hi) => ⌜lo ≤ hi⌝⦄ := by
  vcgen [countInto]
  trace_state
  all_goals grind
