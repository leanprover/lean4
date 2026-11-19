import Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

/-!
The annotations of a loop show the goal at which `vcgen` reaches the loop and the verification
conditions of the loop body and of the loop entry. The verification conditions of the code after
the loop stay at the keyword of the contract. An `invariants` alternative shows the verification
conditions of the loop whose invariant it supplies.
-/

open Std.WP Lean.Order

def countDown (n : Nat) : Id Nat
    ensures r => r = 0 := do
     --^ $/lean/plainGoal
  let mut i := n
  while i > 0
      invariant exit => if exit then i = 0 else True
       --^ $/lean/plainGoal
      decreasing i
       --^ $/lean/plainGoal
    do
    i := i - 1
  return i

def sum (xs : List Nat) : Id Nat
    ensures r => r = xs.sum := do
  let mut acc := 0
  for x in xs invariant pref _ => acc = pref.sum do
             --^ $/lean/plainGoal
    acc := acc + x
  return acc

def sumDef (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do acc := acc + x
  return acc

theorem sumDef_eq (l : List Nat) : sumDef l = l.sum := by
  generalize h : sumDef l = r
  apply Id.of_run_eq_wp h
  vcgen [sumDef] invariants
  · fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
--^ $/lean/plainGoal
       --^ $/lean/plainGoal
  with finish
