import Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

/-!
The info view shows the goal before `vcgen` on its first character and the verification conditions
on the rest of the keyword, also when a `with` clause discharges them. An `invariants` alternative
shows the goal it fills.
-/

open Std.WP Lean.Order

def sumDef (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do acc := acc + x
  return acc

theorem sumDef_eq (l : List Nat) : sumDef l = l.sum := by
  generalize h : sumDef l = r
  apply Id.of_run_eq_wp h
  vcgen [sumDef] invariants
--^ $/lean/plainGoal
 --^ $/lean/plainGoal
  · fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
--^ $/lean/plainGoal
  with finish

theorem sumDef_eq' (l : List Nat) : sumDef l = l.sum := by
  generalize h : sumDef l = r
  apply Id.of_run_eq_wp h
  vcgen [sumDef] invariants
  | inv1 _ suff acc => fun _ _ _ => ⌜acc + suff.sum = l.sum⌝
--^ $/lean/plainGoal
  with finish

/-! The keyword of the first contract clause shows the goals of the `vcgen` call that proves it. -/

def countDown (n : Nat) : Id Nat
    ensures r => r = 0 := do
   --^ $/lean/plainGoal
  let mut i := n
  while i > 0
      invariant exit => if exit then i = 0 else True
      decreasing i
    do
    i := i - 1
  return i
