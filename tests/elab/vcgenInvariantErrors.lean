import Std.WP
set_option experimental.vcgen true

/-!
`vcgen` reports an `invariants` alternative that fails to elaborate once, at the alternative, and
elaborates the alternatives in the context of the enclosing declaration.
-/

open Std.WP Lean.Order

def countDown (n : Nat) : Id Nat := do
  let mut i := n
  while i > 0 do
    i := i - 1
  return i

/-!
`inv1` is the invariant and `inv2` the variant of the loop. Each alternative below has the type of
the other one.
-/

/--
error: typeclass instance problem is stuck
  Assertion ?_

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Assertion` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
---
error: Type mismatch
  WhileInvariant.ofInvariantAndBreak (fun x => ⌜True⌝) fun i => ⌜i = 0⌝
has type
  WhileInvariant Nat ?_
of sort `Type` but is expected to have type
  Variant Nat Prop
of sort `Type (_ + 1)`
-/
#guard_msgs (error) in
set_option pp.mvars false in
theorem countDown_swapped (n : Nat) : ⦃⌜True⌝⦄ countDown n ⦃fun r => ⌜r = 0⌝⦄ := by
  vcgen [countDown] invariants
  · Variant.ofMeasure fun (i : Nat) => i
  · WhileInvariant.ofInvariantAndBreak (fun _ => ⌜True⌝) (fun i => ⌜i = 0⌝)
  all_goals sorry

theorem countDown_spec (n : Nat) : ⦃⌜True⌝⦄ countDown n ⦃fun r => ⌜r = 0⌝⦄ := by
  vcgen [countDown] invariants
  · WhileInvariant.ofInvariantAndBreak (fun _ => ⌜True⌝) (fun i => ⌜i = 0⌝)
  · Variant.ofMeasure fun (i : Nat) => i
  with finish

/-! An ill-typed subterm of an alternative is reported once. -/

def sumDef (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do acc := acc + x
  return acc

/--
error: Type mismatch
  true
has type
  Bool
but is expected to have type
  Nat
-/
#guard_msgs (error) in
theorem sumDef_eq (l : List Nat) : sumDef l = l.sum := by
  generalize h : sumDef l = r
  apply Id.of_run_eq_wp h
  vcgen [sumDef] invariants
  · fun _pref suff acc => ⌜acc + suff.sum = true⌝
  all_goals sorry

/-! An alternative names the universe parameters of the declaration. -/

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
