/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.CommRing.Util
import Lean.Meta.Tactic.Grind.Arith.CommRing.Var

namespace Lean.Meta.Grind.Arith.CommRing

def isAddInst (ring : Ring) (inst : Expr) : Bool :=
  isSameExpr ring.addFn.appArg! inst
def isMulInst (ring : Ring) (inst : Expr) : Bool :=
  isSameExpr ring.mulFn.appArg! inst
def isSubInst (ring : Ring) (inst : Expr) : Bool :=
  isSameExpr ring.subFn.appArg! inst
def isNegInst (ring : Ring) (inst : Expr) : Bool :=
  isSameExpr ring.negFn.appArg! inst
def isPowInst (ring : Ring) (inst : Expr) : Bool :=
  isSameExpr ring.powFn.appArg! inst
def isIntCastInst (ring : Ring) (inst : Expr) : Bool :=
  isSameExpr ring.intCastFn.appArg! inst
def isNatCastInst (ring : Ring) (inst : Expr) : Bool :=
  isSameExpr ring.natCastFn.appArg! inst

private def reportAppIssue (e : Expr) : GoalM Unit := do
  reportIssue! "comm ring term with unexpected instance{indentExpr e}"

/--
Converts a Lean expression `e` in the `CommRing` with id `ringId` into
a `CommRing.Expr` object.

If `skipVar` is `true`, then the result is `none` if `e` is not an interpreted `CommRing` term.
We use `skipVar := false` when processing inequalities, and `skipVar := true` for equalities and disequalities
-/
partial def reify? (e : Expr) (skipVar := true) : RingM (Option RingExpr) := do
  let toVar (e : Expr) : RingM RingExpr := do
    return .var (← mkVar e)
  let asVar (e : Expr) : RingM RingExpr := do
    reportAppIssue e
    return .var (← mkVar e)
  let rec go (e : Expr) : RingM RingExpr := do
    match_expr e with
    | HAdd.hAdd _ _ _ i a b =>
      if isAddInst (← getRing) i then return .add (← go a) (← go b) else asVar e
    | HMul.hMul _ _ _ i a b =>
      if isMulInst (← getRing) i then return .mul (← go a) (← go b) else asVar e
    | HSub.hSub _ _ _ i a b =>
      if isSubInst (← getRing) i then return .sub (← go a) (← go b) else asVar e
    | HPow.hPow _ _ _ i a b =>
      let some k ← getNatValue? b | toVar e
      if isPowInst (← getRing) i then return .pow (← go a) k else asVar e
    | Neg.neg _ i a =>
      if isNegInst (← getRing) i then return .neg (← go a) else asVar e
    | IntCast.intCast _ i a =>
      if isIntCastInst (← getRing) i then
        let some k ← getIntValue? a | toVar e
        return .num k
      else
        asVar e
    | NatCast.natCast _ i a =>
      if isNatCastInst (← getRing) i then
        let some k ← getNatValue? a | toVar e
        return .num k
      else
        asVar e
    | OfNat.ofNat _ n _ =>
      let some k ← getNatValue? n | toVar e
      return .num k
    | _ => toVar e
  let toTopVar (e : Expr) : RingM (Option RingExpr) := do
    if skipVar then
      return none
    else
      return some (← toVar e)
  let asTopVar (e : Expr) : RingM (Option RingExpr) := do
    reportAppIssue e
    toTopVar e
  match_expr e with
  | HAdd.hAdd _ _ _ i a b =>
    if isAddInst (← getRing) i then return some (.add (← go a) (← go b)) else asTopVar e
  | HMul.hMul _ _ _ i a b =>
    if isMulInst (← getRing) i then return some (.mul (← go a) (← go b)) else asTopVar e
  | HSub.hSub _ _ _ i a b =>
    if isSubInst (← getRing) i then return some (.sub (← go a) (← go b)) else asTopVar e
  | HPow.hPow _ _ _ i a b =>
    let some k ← getNatValue? b | return none
    if isPowInst (← getRing) i then return some (.pow (← go a) k) else asTopVar e
  | Neg.neg _ i a =>
    if isNegInst (← getRing) i then return some (.neg (← go a)) else asTopVar e
  | IntCast.intCast _ i a =>
    if isIntCastInst (← getRing) i then
      let some k ← getIntValue? a | toTopVar e
      return some (.num k)
    else
      asTopVar e
  | NatCast.natCast _ i a =>
    if isNatCastInst (← getRing) i then
      let some k ← getNatValue? a | toTopVar e
      return some (.num k)
    else
      asTopVar e
  | OfNat.ofNat _ n _ =>
    let some k ← getNatValue? n | asTopVar e
    return some (.num k)
  | _ => toTopVar e

end  Lean.Meta.Grind.Arith.CommRing
