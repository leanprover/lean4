/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.DSimp.DSimpM
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.Util
import Lean.Meta.WHNF
import Lean.ProjFns
namespace Lean.Meta.Sym.DSimp
open Lean.Meta.Sym.Internal

public def beta : DSimproc := fun e => do
  unless e.isApp do return .rfl
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then
    return .step (← betaRevS f e.getAppRevArgs)
  else
    return .rfl

/--
Unfolds `fvarId` in `e`, where `e` is `fvarId` itself or an application whose head is
`fvarId`. `dsimp` does not visit application heads, so the head position must be
handled here. Beta-reduction of the exposed lambda is left to `beta`.
-/
private def zetaDeltaCore (fvarId : FVarId) (e : Expr) : DSimpM Result := do
  let decl ← fvarId.getDecl
  let some value := decl.value? | return .rfl
  if e.isApp then
    return .step (← mkAppNS value e.getAppArgs)
  else
    return .step value

public def zetaDelta (s : FVarIdSet) : DSimproc := fun e => do
  let .fvar fvarId := e.getAppFn | return .rfl
  unless s.contains fvarId do return .rfl
  zetaDeltaCore fvarId e

public def zetaDeltaAll : DSimproc := fun e => do
  let .fvar fvarId := e.getAppFn | return .rfl
  zetaDeltaCore fvarId e

public def zeta : DSimproc := fun e => do
  let .letE .. := e | return .rfl
  go e #[]
where
  go (e : Expr) (subst : Array Expr) : DSimpM Result := do
    match e with
    | .letE _ _ v b _ => go b (subst.push (← instantiateRevS v subst))
    | _ => return .step (← instantiateRevS e subst)

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
  let e'' ← share e''
  return .step e''

end Lean.Meta.Sym.DSimp
