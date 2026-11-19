import Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

/-!
The info view shows the goal before `vcgen` on its first character and the verification conditions
on the rest of the keyword, also when a `with` clause discharges them. The right-hand side of an
`invariants` alternative has the hole it fills as expected type. An alternative reports its errors
once, at the part that fails, and names the universe parameters of the enclosing declaration.
-/

open Std.WP Lean.Order
--^ collectDiagnostics

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
  --^ $/lean/plainTermGoal
  with finish

theorem sumDef_eq' (l : List Nat) : sumDef l = l.sum := by
  generalize h : sumDef l = r
  apply Id.of_run_eq_wp h
  vcgen [sumDef] invariants
  | inv1 => fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
          --^ $/lean/plainTermGoal
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

/-! `inv1` is the invariant and `inv2` the variant of the loop of `loop`. -/

def loop (n : Nat) : Id Nat := do
  let mut i := n
  while i > 0 do
    i := i - 1
  return i

theorem loop_swapped (n : Nat) : ⦃⌜True⌝⦄ loop n ⦃fun r => ⌜r = 0⌝⦄ := by
  vcgen [loop] invariants
  · Variant.ofMeasure fun (i : Nat) => i
  · WhileInvariant.ofInvariantAndBreak (fun _ => ⌜True⌝) (fun i => ⌜i = 0⌝)
  all_goals sorry

theorem loop_nat (n : Nat) : ⦃⌜True⌝⦄ loop n ⦃fun r => ⌜r = 0⌝⦄ := by
  vcgen [loop] invariants
  | inv1 => (5 : Nat)
  | inv2 => Variant.ofMeasure fun (i : Nat) => i
  | inv3 => ⌜True⌝
  all_goals sorry

theorem sumDef_bool (l : List Nat) : sumDef l = l.sum := by
  generalize h : sumDef l = r
  apply Id.of_run_eq_wp h
  vcgen [sumDef] invariants
  · fun _pref suff acc => ⌜acc + suff.sum = true⌝
  all_goals sorry

theorem sumDef_names (l : List Nat) : sumDef l = l.sum := by
  generalize h : sumDef l = r
  apply Id.of_run_eq_wp h
  vcgen [sumDef] invariants
  | inv1 a b c d e f g h i j k => fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
  all_goals sorry

universe u in
theorem length_eq {α : Type u} (l : List α) : (Id.run do
    let mut n := 0
    for _ in l do n := n + 1
    return n) = l.length := by
  generalize h : (Id.run _ : Nat) = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · fun _pref (suff : List.{u} α) n => ⌜n + suff.length = l.length⌝
  with finish
