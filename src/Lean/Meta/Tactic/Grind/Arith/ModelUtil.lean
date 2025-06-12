/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Std.Internal.Rat
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind.Arith
open Std.Internal
/-!
Helper functions for constructing counterexamples in the `linarith` and `cutsat` modules
-/

/--
Returns `true` if adding the assignment `e := v` to `a` will falsify any asserted disequality in core.
-/
private partial def satisfyDiseqs (goal : Goal) (a : Std.HashMap Expr Rat) (e : Expr) (v : Int) : Bool := Id.run do
  let some parents := goal.parents.find? { expr := e } | return true
  for parent in parents do
    let_expr Eq _ lhs rhs := parent | continue
    let some root := goal.getRoot? parent | continue
    if root.isConstOf ``False then
      let some lhsRoot := goal.getRoot? lhs | continue
      let some rhsRoot := goal.getRoot? rhs | continue
      if lhsRoot == e && !checkDiseq rhsRoot then return false
      if rhsRoot == e && !checkDiseq lhsRoot then return false
  return true
where
  checkDiseq (other : Expr) : Bool :=
    if let some v' := a[other]? then
      v' != v
    else
      true

/--
Returns an integer value `i` for assigning to `e` s.t. adding `e := i` to `a` will not falsify any disequality
and `i` is not in `alreadyUsed`.
-/
partial def pickUnusedValue (goal : Goal) (a : Std.HashMap Expr Rat) (e : Expr) (next : Int) (alreadyUsed : Std.HashSet Int) : Int :=
  go next
where
  go (next : Int) : Int :=
    if alreadyUsed.contains next then
      go (next+1)
    else if satisfyDiseqs goal a e next then
      next
    else
      go (next + 1)

/--
Returns `true` if `e` should be treated as an interpreted value by the arithmetic modules.
-/
def isInterpretedTerm (e : Expr) : Bool :=
  isNatNum e || isIntNum e || e.isAppOf ``HAdd.hAdd || e.isAppOf ``HMul.hMul || e.isAppOf ``HSub.hSub
  || e.isAppOf ``Neg.neg || e.isAppOf ``HDiv.hDiv || e.isAppOf ``HMod.hMod || e.isAppOf ``One.one || e.isAppOf ``Zero.zero
  || e.isAppOf ``NatCast.natCast || e.isIte || e.isDIte

/--
Adds the assignments `e' := v` to `a` for each `e'` in the equivalence class os `e`.
-/
def assignEqc (goal : Goal) (e : Expr) (v : Rat) (a : Std.HashMap Expr Rat) : Std.HashMap Expr Rat := Id.run do
  let mut a := a
  for e in goal.getEqc e do
    a := a.insert e v
  return a

end Lean.Meta.Grind.Arith
