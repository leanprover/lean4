/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Rewrite

namespace Lean.Meta
namespace Simp

private def join (p₁? p₂? : Option Expr) : MetaM (Option Expr) :=
  match p₁? with
  | none    => return p₂?
  | some p₁ => match p₂? with
    | none    => return p₁?
    | some p₂ => return some (← mkEqTrans p₁ p₂)

private def mkEqTrans (r₁ r₂ : Result) : MetaM Result := do
  match r₁.proof? with
  | none => return r₂
  | some p₁ => match r₂.proof? with
    | none    => return { r₂ with proof? := r₁.proof? }
    | some p₂ => return { r₂ with proof? := (← Meta.mkEqTrans p₁ p₂) }

private def mkCongrFun (r : Result) (a : Expr) : MetaM Result :=
  match r.proof? with
  | none   => return { expr := mkApp r.expr a, proof? := none }
  | some h => return { expr := mkApp r.expr a, proof? := (← Meta.mkCongrFun h a) }

private def mkCongr (r₁ r₂ : Result) : MetaM Result :=
  let e := mkApp r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none }
  | some h,  none    => return { expr := e, proof? := (← Meta.mkCongrFun h r₂.expr) }
  | none,    some h  => return { expr := e, proof? := (← Meta.mkCongrArg r₁.expr h) }
  | some h₁, some h₂ => return { expr := e, proof? := (← Meta.mkCongr h₁ h₂) }

private def reduceProj (e : Expr) : MetaM Expr := do
  match (← reduceProj? e) with
  | some e => return e
  | _      => return e

private def reduceProjFn? (e : Expr) : MetaM (Option Expr) := do
  matchConst e.getAppFn (fun _ => pure none) fun cinfo _ => do
    if !(← isProjectionFn cinfo.name) then
      return none
    else match (← unfoldDefinition? e) with
      | none   => pure none
      | some e =>
        match (← reduceProj? e.getAppFn) with
        | some f => return some (mkAppN f e.getAppArgs)
        | none   => return none

private def reduceFVar (cfg : Config) (e : Expr) : MetaM Expr := do
  if cfg.zeta then
    match (← getFVarLocalDecl e).value? with
    | some v => return v
    | none   => return e
  else
    return e

private partial def reduce (cfg : Config) (e : Expr) : MetaM Expr := withIncRecDepth do
  if cfg.beta then
    let e' := e.headBeta
    if e' != e then
      return (← reduce cfg e')
  -- TODO: eta reduction
  if cfg.proj then
    match (← reduceProjFn? e) with
    | some e => return (← reduce cfg e)
    | none   => pure ()
  if cfg.iota then
    match (← reduceRecMatcher? e) with
    | some e => return (← reduce cfg e)
    | none   => pure ()
  return e

private partial def dsimp (e : Expr) : M σ Expr := do
  return e -- TODO

partial def simp {σ} (e : Expr) : M σ Result := withIncRecDepth do
  let cfg ← getConfig
  if cfg.memoize then
    if let some result := (← get).cache.find? e then
      return result
  simpLoop { expr := e }

where
  simpLoop (r : Result) : M σ Result := do
    let cfg ← getConfig
    if (← get).numSteps > cfg.maxSteps then
      throwError! "simp failed, maximum number of steps exceeded"
    else
      modify fun s => { s with numSteps := s.numSteps + 1 }
      match (← pre r.expr) with
      | Step.done r   => cacheResult cfg r
      | Step.visit r' =>
        let r ← mkEqTrans r r'
        let r ← mkEqTrans r (← simpStep r.expr)
        let e := r.expr
        match (← post e) with
        | Step.done r'  => cacheResult cfg (← mkEqTrans r r')
        | Step.visit r' =>
          let r ← mkEqTrans r r'
          if cfg.singlePass || e == r.expr then
            cacheResult cfg r
          else
            simpLoop r

  simpStep (e : Expr) : M σ Result := do
    match e with
    | Expr.mdata _ e _ => simp e
    | Expr.proj ..     => pure { expr := (← reduceProj e) }
    | Expr.app ..      => simpApp e
    | Expr.lam ..      => simpLambda e
    | Expr.forallE ..  => simpForall e
    | Expr.letE ..     => simpLet e
    | Expr.const ..    => pure { expr := e }
    | Expr.bvar ..     => unreachable!
    | Expr.sort ..     => pure { expr := e }
    | Expr.lit ..      => pure { expr := e }
    | Expr.mvar ..     => pure { expr := (← instantiateMVars e) }
    | Expr.fvar ..     => pure { expr := (← reduceFVar (← getConfig) e) }

  simpApp (e : Expr) : M σ Result := do
    let e ← reduce (← getConfig) e
    if !e.isApp then
      simp e
    else
      withParent e <| e.withApp fun f args => do
        let infos := (← getFunInfoNArgs f args.size).paramInfo
        let mut r ← simp f
        let mut i := 0
        for arg in args do
          if i < infos.size && !infos[i].hasFwdDeps then
            r ← mkCongr r (← simp arg)
          else
            r ← mkCongrFun r (← dsimp arg)
          i := i + 1
        return r

  simpLambda (e : Expr) : M σ Result :=
    return { expr := e } -- TODO

  simpForall (e : Expr) : M σ Result :=
    return { expr := e } -- TODO

  simpLet (e : Expr) : M σ Result :=
    return { expr := e } -- TODO

  cacheResult (cfg : Config) (r : Result) : M σ Result := do
    if cfg.memoize then
      modify fun s => { s with cache := s.cache.insert e r }
    return r

def main (e : Expr) (s : σ) (config : Config := {}) (methods : Methods σ := {}) (simpLemmas : SimpLemmas := {}) : MetaM Result := do
  withReducible do
    simp e methods { config := config, simpLemmas := simpLemmas } |>.run' { user := s }

end Simp

def simp (e : Expr) (simpLemmas : SimpLemmas := {}) : MetaM Simp.Result := do
  let discharge? (e : Expr) : SimpM Unit (Option Expr) := return none -- TODO: use simp, and add config option
  let pre  := (Simp.preDefault · discharge?)
  let post := (Simp.postDefault · discharge?)
  Simp.main e () (methods := { pre := pre, post := post, discharge? := discharge? }) (simpLemmas := simpLemmas)

end Lean.Meta
