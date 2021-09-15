/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.InferType

namespace Lean.Meta

@[inline] private def checkFunInfoCache (fn : Expr) (maxArgs? : Option Nat) (k : MetaM FunInfo) : MetaM FunInfo := do
  let s ← get
  let t ← getTransparency
  match s.cache.funInfo.find? ⟨t, fn, maxArgs?⟩ with
  | some finfo => pure finfo
  | none       => do
    let finfo ← k
    modify fun s => { s with cache := { s.cache with funInfo := s.cache.funInfo.insert ⟨t, fn, maxArgs?⟩ finfo } }
    pure finfo

@[inline] private def whenHasVar {α} (e : Expr) (deps : α) (k : α → α) : α :=
  if e.hasFVar then k deps else deps

private def collectDeps (fvars : Array Expr) (e : Expr) : Array Nat :=
  let rec visit : Expr → Array Nat → Array Nat
    | e@(Expr.app f a _),       deps => whenHasVar e deps (visit a ∘ visit f)
    | e@(Expr.forallE _ d b _), deps => whenHasVar e deps (visit b ∘ visit d)
    | e@(Expr.lam _ d b _),     deps => whenHasVar e deps (visit b ∘ visit d)
    | e@(Expr.letE _ t v b _),  deps => whenHasVar e deps (visit b ∘ visit v ∘ visit t)
    | Expr.proj _ _ e _,        deps => visit e deps
    | Expr.mdata _ e _,         deps => visit e deps
    | e@(Expr.fvar _ _),        deps =>
      match fvars.indexOf? e with
      | none   => deps
      | some i => if deps.contains i.val then deps else deps.push i.val
    | _,                        deps => deps
  let deps := visit e #[]
  deps.qsort (fun i j => i < j)

/-- Update `hasFwdDeps` fields using new `backDeps` -/
private def updateHasFwdDeps (pinfo : Array ParamInfo) (backDeps : Array Nat) : Array ParamInfo :=
  if backDeps.size == 0 then
    pinfo
  else
    -- update hasFwdDeps fields
    pinfo.mapIdx fun i info =>
      if info.hasFwdDeps then info
      else if backDeps.contains i then
        { info with hasFwdDeps := true }
      else
        info

private def getFunInfoAux (fn : Expr) (maxArgs? : Option Nat) : MetaM FunInfo :=
  checkFunInfoCache fn maxArgs? do
    let fnType ← inferType fn
    withTransparency TransparencyMode.default do
      forallBoundedTelescope fnType maxArgs? fun fvars type => do
        let mut pinfo := #[]
        for i in [:fvars.size] do
          let fvar := fvars[i]
          let decl ← getFVarLocalDecl fvar
          let backDeps := collectDeps fvars decl.type
          pinfo := updateHasFwdDeps pinfo backDeps
          pinfo := pinfo.push {
            backDeps     := backDeps
            binderInfo   := decl.binderInfo
          }
        let resultDeps := collectDeps fvars type
        pinfo := updateHasFwdDeps pinfo resultDeps
        pure { resultDeps := resultDeps, paramInfo := pinfo }

def getFunInfo (fn : Expr) : MetaM FunInfo :=
  getFunInfoAux fn none

def getFunInfoNArgs (fn : Expr) (nargs : Nat) : MetaM FunInfo :=
  getFunInfoAux fn (some nargs)

def FunInfo.getArity (info : FunInfo) : Nat :=
  info.paramInfo.size

end Lean.Meta
