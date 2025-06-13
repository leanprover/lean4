/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.Linear.Var

namespace Lean.Meta.Grind.Arith.Linear

def isAddInst (struct : Struct) (inst : Expr) : Bool :=
  isSameExpr struct.addFn.appArg! inst
def isZeroInst (struct : Struct) (inst : Expr) : Bool :=
  isSameExpr struct.zero.appArg! inst
def isHMulInst (struct : Struct) (inst : Expr) : Bool :=
  isSameExpr struct.hmulFn.appArg! inst
def isHMulNatInst (struct : Struct) (inst : Expr) : Bool :=
  isSameExpr struct.hmulNatFn.appArg! inst
def isSMulInst (struct : Struct) (inst : Expr) : Bool :=
  if let some smulFn := struct.smulFn? then
    isSameExpr smulFn.appArg! inst
  else
    false
def isSubInst (struct : Struct) (inst : Expr) : Bool :=
  isSameExpr struct.subFn.appArg! inst
def isNegInst (struct : Struct) (inst : Expr) : Bool :=
  isSameExpr struct.negFn.appArg! inst

def reportInstIssue (e : Expr) : GoalM Unit := do
  reportIssue! "`grind linarith` term with unexpected instance{indentExpr e}"

/--
Converts a Lean `IntModule` expression `e` into a `LinExpr`

If `skipVar` is `true`, then the result is `none` if `e` is not an interpreted `IntModule` term.
We use `skipVar := false` when processing inequalities, and `skipVar := true` for equalities and disequalities
-/
partial def reify? (e : Expr) (skipVar : Bool) : LinearM (Option LinExpr) := do
  match_expr e with
  | HAdd.hAdd _ _ _ i a b =>
    if isAddInst (← getStruct  ) i then return some (.add (← go a) (← go b)) else asTopVar e
  | HSub.hSub _ _ _ i a b =>
    if isSubInst (← getStruct  ) i then return some (.sub (← go a) (← go b)) else asTopVar e
  | HMul.hMul _ _ _ i a b =>
    let some r ← processHMul i a b | asTopVar e
    return some r
  | HSMul.hSMul _ _ _ i a b =>
    if isSMulInst (← getStruct) i then
      let some k ← getIntValue? a | pure ()
      return some (.mul k (← go b))
    asTopVar e
  | Neg.neg _ i a =>
    if isNegInst (← getStruct  ) i then return some (.neg (← go a)) else asTopVar e
  | Zero.zero _ i =>
    if isZeroInst (← getStruct) i then return some .zero else asTopVar e
  | OfNat.ofNat _ _ _ =>
    if (← isOfNatZero e) then return some .zero else asTopVar e
  | _ =>
    if skipVar then
      return none
    else
      return some (← toVar e)
where
  toVar (e : Expr) : LinearM LinExpr := do
    return .var (← mkVar e)
  asVar (e : Expr) : LinearM LinExpr := do
    reportInstIssue e
    return .var (← mkVar e)
  asTopVar (e : Expr) : LinearM (Option LinExpr) := do
    reportInstIssue e
    if skipVar then
      return none
    else
      return some (← asVar e)
  isOfNatZero (e : Expr) : LinearM Bool := do
    withDefault <| isDefEq e (← getStruct).ofNatZero
  processHMul (i a b : Expr) : LinearM (Option LinExpr) := do
    if isHMulInst (← getStruct) i then
      let some k ← getIntValue? a | return none
      return some (.mul k (← go b))
    else if isHMulNatInst (← getStruct) i then
      let some k ← getNatValue? a | return none
      return some (.mul k (← go b))
    return none
  go (e : Expr) : LinearM LinExpr := do
    match_expr e with
    | HAdd.hAdd _ _ _ i a b =>
      if isAddInst (← getStruct) i then return .add (← go a) (← go b) else asVar e
    | HSub.hSub _ _ _ i a b =>
      if isSubInst (← getStruct) i then return .sub (← go a) (← go b) else asVar e
    | HMul.hMul _ _ _ i a b =>
      let some r ← processHMul i a b | asVar e
      return r
    | HSMul.hSMul _ _ _ i a b =>
      if isSMulInst (← getStruct) i then
        let some k ← getIntValue? a | pure ()
        return .mul k (← go b)
      asVar e
    | Neg.neg _ i a =>
      if isNegInst (← getStruct) i then return .neg (← go a) else asVar e
    | Zero.zero _ i =>
      if isZeroInst (← getStruct) i then return .zero else asVar e
    | OfNat.ofNat _ _ _ =>
      if (← isOfNatZero e) then return .zero else toVar e
    | _ => toVar e


end  Lean.Meta.Grind.Arith.Linear
