/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.Util.MonadCache
import Lean.Meta.Basic

namespace Lean.Meta
namespace ForEachExpr

abbrev M := MonadCacheT Expr Unit MetaM

mutual

private partial def visitBinder (fn : Expr → MetaM Bool) : Array Expr → Nat → Expr → M Unit
  | fvars, j, Expr.lam n d b c => do
    let d := d.instantiateRevRange j fvars.size fvars;
    visit fn d;
    withLocalDecl n c.binderInfo d fun x =>
      visitBinder fn (fvars.push x) j b
  | fvars, j, Expr.forallE n d b c => do
    let d := d.instantiateRevRange j fvars.size fvars;
    visit fn d;
    withLocalDecl n c.binderInfo d fun x =>
      visitBinder fn (fvars.push x) j b
  | fvars, j, Expr.letE n t v b _ => do
    let t := t.instantiateRevRange j fvars.size fvars;
    visit fn t;
    let v := v.instantiateRevRange j fvars.size fvars;
    visit fn v;
    withLetDecl n t v fun x =>
      visitBinder fn (fvars.push x) j b
  | fvars, j, e => visit fn $ e.instantiateRevRange j fvars.size fvars

partial def visit (fn : Expr → MetaM Bool) (e : Expr) : M Unit :=
  checkCache e fun _ => do
    if (← liftM (fn e)) then
      match e with
      | Expr.forallE _ _ _ _   => visitBinder fn #[] 0 e
      | Expr.lam _ _ _ _       => visitBinder fn #[] 0 e
      | Expr.letE _ _ _ _ _    => visitBinder fn #[] 0 e
      | Expr.app f a _         => visit fn f; visit fn a
      | Expr.mdata _ b _       => visit fn b
      | Expr.proj _ _ b _      => visit fn b
      | _                      => pure ()

end

end ForEachExpr

/-- Similar to `Expr.forEach'`, but creates free variables whenever going inside of a binder. -/
def forEachExpr' (e : Expr) (f : Expr → MetaM Bool) : MetaM Unit :=
  ForEachExpr.visit f e |>.run

/-- Similar to `Expr.forEach`, but creates free variables whenever going inside of a binder. -/
def forEachExpr (e : Expr) (f : Expr → MetaM Unit) : MetaM Unit :=
  forEachExpr' e fun e => do
    f e
    pure true

/--
  Similar to `mkForallFVars`, but tries to infer better binder names when `xs` contains metavariables.
  Let `?m` be a metavariable in `xs` s.t. `?m` does not have a user facing name.
  Then, we try to find an application `f ... ?m` in the other binder typer and `type`, and
  (temporarily) use the corresponding parameter name (with a fresh macro scope) as the user facing name for `?m`.
  The "renaming" is temporary.
-/
def mkForallFVars' (xs : Array Expr) (type : Expr) : MetaM Expr := do
  if (← xs.anyM shouldInferBinderName) then
    let toReset ← IO.mkRef #[]
    try
      for x in xs do
        visit (← inferType x) toReset
      visit type toReset
      mkForallFVars xs type
    finally
      for mvarId in (← toReset.get) do
        modifyMCtx fun mctx => mctx.setMVarUserNameTemporarily mvarId Name.anonymous
  else
    mkForallFVars xs type
where
  shouldInferBinderName (x : Expr) : MetaM Bool := do
    match x with
    | .mvar mvarId _ => return (← Meta.getMVarDecl mvarId).userName.isAnonymous
    | _ => return false

  visit (e : Expr) (toReset : IO.Ref (Array MVarId)) : MetaM Unit := do
    forEachExpr (← instantiateMVars e) fun e => do
      if e.isApp then
        let args := e.getAppArgs
        for i in [:args.size] do
          let arg := args[i]
          if arg.isMVar && xs.contains arg then
            let mvarId := arg.mvarId!
            if (← Meta.getMVarDecl mvarId).userName.isAnonymous then
              forallBoundedTelescope (← inferType e.getAppFn) (some (i+1)) fun xs _ => do
                if i < xs.size then
                  let mvarId := arg.mvarId!
                  let userName ← mkFreshUserName (← getFVarLocalDecl xs[i]).userName
                  toReset.modify (·.push mvarId)
                  modifyMCtx fun mctx => mctx.setMVarUserNameTemporarily mvarId userName

end Lean.Meta
