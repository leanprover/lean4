/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic
import Init.Lean.Meta.InferType

namespace Lean
namespace Meta

@[inline] private def checkFunInfoCache (fn : Expr) (maxArgs? : Option Nat) (k : MetaM FunInfo) : MetaM FunInfo := do
s ← get;
t ← getTransparency;
match s.cache.funInfo.find ⟨t, fn, maxArgs?⟩ with
| some finfo => pure finfo
| none       => do
  finfo ← k;
  modify $ fun s => { cache := { funInfo := s.cache.funInfo.insert ⟨t, fn, maxArgs?⟩ finfo, .. s.cache }, .. s };
  pure finfo

@[inline] private def whenHasVar {α} (e : Expr) (deps : α) (k : α → α) : α :=
if e.hasFVar then k deps else deps

private def collectDepsAux (fvars : Array Expr) : Expr → Array Nat → Array Nat
| e@(Expr.app f a _),       deps => whenHasVar e deps (collectDepsAux a ∘ collectDepsAux f)
| e@(Expr.forallE _ d b _), deps => whenHasVar e deps (collectDepsAux b ∘ collectDepsAux d)
| e@(Expr.lam _ d b _),     deps => whenHasVar e deps (collectDepsAux b ∘ collectDepsAux d)
| e@(Expr.letE _ t v b _),  deps => whenHasVar e deps (collectDepsAux b ∘ collectDepsAux v ∘ collectDepsAux t)
| Expr.proj _ _ e _,        deps => collectDepsAux e deps
| Expr.mdata _ e _,         deps => collectDepsAux e deps
| e@(Expr.fvar _ _),        deps =>
  match fvars.indexOf e with
  | none   => deps
  | some i => if deps.contains i.val then deps else deps.push i.val
| _,                        deps => deps

private def collectDeps (fvars : Array Expr) (e : Expr) : Array Nat :=
let deps := collectDepsAux fvars e #[];
deps.qsort (fun i j => i < j)

/-- Update `hasFwdDeps` fields using new `backDeps` -/
private def updateHasFwdDeps (pinfo : Array ParamInfo) (backDeps : Array Nat) : Array ParamInfo :=
if backDeps.size == 0 then
  pinfo
else
  -- update hasFwdDeps fields
  pinfo.mapIdx $ fun i info =>
    if info.hasFwdDeps then info
    else if backDeps.contains i then
      { hasFwdDeps := true, .. info }
    else
      info

private def getFunInfoAux (fn : Expr) (maxArgs? : Option Nat) : MetaM FunInfo :=
checkFunInfoCache fn maxArgs? $ do
  fnType ← inferType fn;
  withTransparency TransparencyMode.default $
    forallBoundedTelescope fnType maxArgs? $ fun fvars type => do
      pinfo ← fvars.size.foldM
        (fun (i : Nat) (pinfo : Array ParamInfo) => do
          let fvar := fvars.get! i;
          decl ← getFVarLocalDecl fvar;
          let backDeps := collectDeps fvars decl.type;
          let pinfo    := updateHasFwdDeps pinfo backDeps;
          pure $ pinfo.push {
            backDeps     := backDeps,
            implicit     := decl.binderInfo == BinderInfo.implicit,
            instImplicit := decl.binderInfo == BinderInfo.instImplicit })
        #[];
      let resultDeps := collectDeps fvars type;
      let pinfo      := updateHasFwdDeps pinfo resultDeps;
      pure { resultDeps := resultDeps, paramInfo := pinfo }

def getFunInfo (fn : Expr) : MetaM FunInfo :=
getFunInfoAux fn none

def getFunInfoNArgs (fn : Expr) (nargs : Nat) : MetaM FunInfo :=
getFunInfoAux fn (some nargs)

end Meta
end Lean
