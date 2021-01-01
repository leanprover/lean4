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


mutual
  partial def dsimp (e : Expr) : M σ Expr :=
    return e -- TODO

  partial def reduce (e : Expr) : M σ Expr :=
    return e -- TODO

  partial def simp {σ} (e : Expr) : M σ Result := withIncRecDepth do
    let cfg ← getConfig
    if cfg.memoize then
      if let some result := (← get).cache.find? e then
        return result
    if (← get).numSteps > cfg.maxSteps then
       throwError! "simp failed, maximum number of steps exceeded"
    modify fun s => { s with numSteps := s.numSteps + 1 }
    match (← pre e) with
    | Step.done r  => cacheResult cfg r
    | Step.visit r => simpLoop r

  where
    simpLoop (r : Result) : M σ Result := do
      let r ← mkEqTrans r (← simpStep r.expr)
      let cfg ← getConfig
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
      | Expr.proj ..     => simpProj e
      | Expr.app ..      => simpApp e
      | Expr.lam ..      => simpLambda e
      | Expr.forallE ..  => simpForall e
      | Expr.letE ..     => simpLet e
      | Expr.const ..    => simpConst e
      | Expr.bvar ..     => unreachable!
      | Expr.sort ..     => pure { expr := e }
      | Expr.lit ..      => pure { expr := e }
      | Expr.mvar ..     => simpMVar e
      | Expr.fvar ..     => simpFVar e

    simpProj (e : Expr) : M σ Result :=
      return { expr := e } -- TODO

    simpApp (e : Expr) : M σ Result := do
      let e ← reduce e
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
              r ← mkCongrFun r arg
            i := i + 1
          return r

    simpLambda (e : Expr) : M σ Result :=
      return { expr := e } -- TODO

    simpForall (e : Expr) : M σ Result :=
      return { expr := e } -- TODO

    simpLet (e : Expr) : M σ Result :=
      return { expr := e } -- TODO

    simpConst (e : Expr) : M σ Result :=
      return { expr := e } -- TODO

    simpMVar (e : Expr) : M σ Result :=
      return { expr := e } -- TODO

    simpFVar (e : Expr) : M σ Result := do
      if (← getConfig).zeta then
        match (← getFVarLocalDecl e).value? with
        | some v => simp v
        | none   => return { expr := e }
      else
        return { expr := e }

    cacheResult (cfg : Config) (r : Result) : M σ Result := do
      if cfg.memoize then
        modify fun s => { s with cache := s.cache.insert e r }
      return r
end

def main (e : Expr) (s : σ) (config : Config := {}) (methods : Methods σ := {}) (simpLemmas : SimpLemmas := {}) : MetaM Result := do
  simp e methods { config := config, simpLemmas := simpLemmas } |>.run' { user := s }

end Simp

def simp (e : Expr) (simpLemmas : SimpLemmas := {}) : MetaM Simp.Result := do
  let discharge? (e : Expr) : SimpM Unit (Option Expr) := return none -- TODO: use simp, and add config option
  let pre  := (Simp.preDefault · discharge?)
  let post := (Simp.postDefault · discharge?)
  Simp.main e () (methods := { pre := pre, post := post, discharge? := discharge? }) (simpLemmas := simpLemmas)

end Lean.Meta
