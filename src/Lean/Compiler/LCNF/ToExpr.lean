/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Basic

namespace Lean.Compiler.LCNF

namespace ToExpr

private abbrev LevelMap := FVarIdMap Nat

private def _root_.Lean.FVarId.toExpr (offset : Nat) (m : LevelMap) (fvarId : FVarId) : Expr :=
  match m.find? fvarId with
  | some level => .bvar (offset - level - 1)
  | none => .fvar fvarId

private def _root_.Lean.Expr.abstract' (offset : Nat) (m : LevelMap) (e : Expr) : Expr :=
  go offset e
where
  go (o : Nat) (e : Expr) : Expr :=
    match e with
    | .fvar fvarId => fvarId.toExpr o m
    | .lit .. | .const .. | .sort .. | .mvar .. | .bvar .. => e
    | .app f a => .app (go o f) (go o a)
    | .mdata k b => .mdata k (go o b)
    | .proj s i b => .proj s i (go o b)
    | .forallE n d b bi => .forallE n (go o d) (go (o+1) b) bi
    | .lam n d b bi => .lam n (go o d) (go (o+1) b) bi
    | .letE n t v b nd => .letE n (go o t) (go o v) (go (o+1) b) nd

abbrev M := ReaderT Nat $ StateM LevelMap

private abbrev mkLambdaM (params : Array Param) (e : Expr) : M Expr :=
  return go (← read) (← get) params.size e
where
  go (offset : Nat) (m : LevelMap) (i : Nat) (e : Expr) : Expr :=
   if i > 0 then
     let param  := params[i-1]!
     let domain := param.type.abstract' (offset - 1) m
     go (offset - 1) m (i - 1) (.lam param.binderName domain e .default)
   else
     e

@[inline] private def _root_.Lean.FVarId.toExprM (fvarId : FVarId) : M Expr :=
  return fvarId.toExpr (← read) (← get)

@[inline] private def _root_.Lean.Expr.abstractM (e : Expr) : M Expr :=
  return e.abstract' (← read) (← get)

@[inline] def withFVar (fvarId : FVarId) (k : M α) : M α := do
  let offset ← read
  modify fun s => s.insert fvarId offset
  withReader (·+1) k

@[inline] partial def withParams (params : Array Param) (k : M α) : M α :=
  go 0
where
  @[specialize] go (i : Nat) : M α := do
    if h : i < params.size then
      withFVar params[i].fvarId (go (i+1))
    else
      k

end ToExpr

open ToExpr

partial def Code.toExprM (code : Code) : M Expr := do
  match code with
  | .let decl k =>
    let type ← decl.type.abstractM
    let value ← decl.value.abstractM
    let body ← withFVar decl.fvarId k.toExprM
    return .letE decl.binderName type value body true
  | .fun decl k | .jp decl k =>
    let type ← decl.type.abstractM
    let value ← withParams decl.params do mkLambdaM decl.params (← decl.value.toExprM)
    let body ← withFVar decl.fvarId k.toExprM
    return .letE decl.binderName type value body true
  | .return fvarId => fvarId.toExprM
  | .jmp fvarId args => return mkAppN (← fvarId.toExprM) (← args.mapM (·.abstractM))
  | .unreach type => return mkApp (mkConst ``lcUnreachable) (← type.abstractM)
  | .cases c =>
    let alts ← c.alts.mapM fun
      | .alt _ params k => withParams params do mkLambdaM params (← k.toExprM)
      | .default k => k.toExprM
    return mkAppN (mkConst `cases) (#[← c.discr.toExprM] ++ alts)

def Code.toExpr (code : Code) : Expr :=
  code.toExprM |>.run 0 |>.run' {}

end Lean.Compiler.LCNF