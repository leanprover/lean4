/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Guard
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.colon]
public def fmtGuardColon : Fmt := fun stx => do fmt (← getStxArg! stx 0)

@[builtin_fmt Lean.Parser.colonEq]
public def fmtGuardColonEq : Fmt := fun stx => do fmt (← getStxArg! stx 0)

@[builtin_fmt Lean.Parser.equal]
public def fmtGuardEqual : Fmt := fun stx => do fmt (← getStxArg! stx 0)

public def fmtGuardExprLike (guardExprTk lhs equal rhs : Syntax) : FmtM TaggedDoc := do
  let guardExprTk ← fmt guardExprTk
  let lhs ← fmt lhs
  let equal ← fmt equal
  let rhs ← fmt rhs
  let equation := Layouts.infixOperator #[lhs, equal, rhs]
  return Layouts.pseudoApplication #[guardExprTk, equation]

@[builtin_fmt Lean.Parser.Tactic.guardExpr]
public def fmtGuardExpr : Fmt := fun
  | `(Parser.Tactic.guardExpr| guard_expr%$guardExprTk $lhs:term $equal:equal $rhs:term) =>
    fmtGuardExprLike guardExprTk lhs equal rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.guardExprConv]
public def fmtGuardExprConv : Fmt := fun
  | `(Parser.Tactic.guardExprConv| guard_expr%$guardExprTk $lhs:term $equal:equal $rhs:term) =>
    fmtGuardExprLike guardExprTk lhs equal rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.guardExprCmd]
public def fmtGuardExprCmd : Fmt := fun
  | `(Parser.Command.guardExprCmd| #guard_expr%$guardExprTk $lhs:term $equal:equal $rhs:term) =>
    fmtGuardExprLike guardExprTk lhs equal rhs
  | _ => throw .partialFormatter

public def fmtGuardTargetLike (guardTargetTk equal rhs : Syntax) : FmtM TaggedDoc := do
  let guardTargetTk ← fmt guardTargetTk
  let equal ← fmt equal
  let rhs ← fmt rhs
  let equation := Layouts.prefixOperator equal rhs .withSpacing
  return Layouts.pseudoApplication #[guardTargetTk, equation]

@[builtin_fmt Lean.Parser.Tactic.guardTarget]
public def fmtGuardTarget : Fmt := fun
  | `(Parser.Tactic.guardTarget| guard_target%$guardTargetTk $equal:equal $rhs:term) =>
    fmtGuardTargetLike guardTargetTk equal rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.guardTargetConv]
public def fmtGuardTargetConv : Fmt := fun
  | `(Parser.Tactic.guardTargetConv| guard_target%$guardTargetTk $equal:equal $rhs:term) =>
    fmtGuardTargetLike guardTargetTk equal rhs
  | _ => throw .partialFormatter

public def fmtGuardHypLike (guardHypTk hyp : Syntax) (colon? type? colonEq? value? : Option Syntax)
    : FmtM TaggedDoc := do
  let guardHypTk ← fmt guardHypTk
  let hyp ← fmt hyp
  let colon? ← fmt? colon?
  let type? ← fmt? type?
  let colonEq? ← fmt? colonEq?
  let value? ← fmt? value?
  let typedHyp := Layouts.typeAscription hyp colon? type?
  let assignedHyp := Layouts.infixOperator #[typedHyp, colonEq?, value?]
  return Layouts.pseudoApplication #[guardHypTk, assignedHyp]

@[builtin_fmt Lean.Parser.Tactic.guardHyp]
public def fmtGuardHyp : Fmt := fun
  | `(Parser.Tactic.guardHyp|
      guard_hyp%$guardHypTk $hyp:term $[$colon?:colon $type?:term]? $[$colonEq?:colonEq $value?:term]?) =>
    fmtGuardHypLike guardHypTk hyp colon? type? colonEq? value?
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.guardHypConv]
public def fmtGuardHypConv : Fmt := fun
  | `(Parser.Tactic.guardHypConv|
      guard_hyp%$guardHypTk $hyp:term $[$colon?:colon $type?:term]? $[$colonEq?:colonEq $value?:term]?) =>
    fmtGuardHypLike guardHypTk hyp colon? type? colonEq? value?
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.guardCmd]
public def fmtGuardCmd : Fmt := fun
  | `(Parser.Command.guardCmd| #guard%$guardTk $t:term) => do
    let guardTk ← fmt guardTk
    let t ← fmt t
    return Layouts.pseudoApplication #[guardTk, t]
  | _ => throw .partialFormatter
