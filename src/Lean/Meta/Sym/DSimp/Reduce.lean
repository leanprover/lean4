/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.DSimp.DSimpM
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.Util
import Lean.Meta.WHNF
import Lean.ProjFns
namespace Lean.Meta.Sym.DSimp

public def beta : DSimproc := fun e => do
  unless e.isApp do return .rfl
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then
    return .step (← betaRevS f e.getAppRevArgs)
  else
    return .rfl

public def zeta (s : FVarIdSet) : DSimproc := fun e => do
  let .fvar fvarId := e | return .rfl
  unless s.contains fvarId do return .rfl
  let decl ← fvarId.getDecl
  let some value := decl.value? | return .rfl
  return .step value

public def zetaAll : DSimproc := fun e => do
  let .fvar fvarId := e | return .rfl
  let decl ← fvarId.getDecl
  let some value := decl.value? | return .rfl
  return .step value

public def dsimpProj : DSimproc := fun e => do
  let f := e.getAppFn
  let .const declName _ := f | return .rfl
  let some _projInfo ← getProjectionFnInfo? declName | return .rfl
  let reduceProjCont? (e? : Option Expr) : DSimpM Result := do
    match e? with
    | none   => return .rfl
    | some e =>
      match (← reduceProj? e.getAppFn) with
      | some f => return .step (← shareCommon (mkAppN f e.getAppArgs))
      | none   => return .rfl
  -- TODO: special support for instances?
  reduceProjCont? (← unfoldDefinition? e)

public def dsimpMatch : DSimproc := fun e => do
  let some e' ← reduceRecMatcher? e | return .rfl
  -- Iota-reduction may expose kernel `Expr.proj` terms via struct-eta,
  -- which the structural simplifier cannot consume directly.
  let e'' ← Sym.foldProjs e'
  if isSameExpr e' e'' then
    return .rfl
  else
    return .step (← share e'')

end Lean.Meta.Sym.DSimp
