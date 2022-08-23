/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.Util.MonadCache
import Lean.Meta.Basic

namespace Lean.Meta

variable {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]

/-- Similar to `Expr.forEach'`, but creates free variables whenever going inside of a binder.
If the inner function returns `false`, deeper subexpressions will not be visited.
 -/
partial def forEachExpr'
  (input : Expr)
  (fn : Expr → m Bool)
  : m Unit := do
  let _ : STWorld IO.RealWorld m := ⟨⟩
  let _ : MonadLiftT (ST IO.RealWorld) m := { monadLift := fun x => liftM (m := MetaM) (liftM (m := ST IO.RealWorld) x) }
  let rec visit (e : Expr) : MonadCacheT Expr Unit m Unit :=
    let rec visitBinder (fvars : Array Expr) (j : Nat) : Expr → MonadCacheT Expr Unit m Unit
      | Expr.lam n d b c => do
        let d := d.instantiateRevRange j fvars.size fvars
        visit d
        withLocalDecl n c d fun x =>
          visitBinder (fvars.push x) j b
      | Expr.forallE n d b c => do
        let d := d.instantiateRevRange j fvars.size fvars
        visit d
        withLocalDecl n c d fun x =>
          visitBinder (fvars.push x) j b
      | Expr.letE n t v b _ => do
        let t := t.instantiateRevRange j fvars.size fvars
        visit t
        let v := v.instantiateRevRange j fvars.size fvars
        visit v
        withLetDecl n t v fun x =>
          visitBinder (fvars.push x) j b
      | e => visit $ e.instantiateRevRange j fvars.size fvars
    checkCache e fun _ => do
      if (← liftM (fn e)) then
        match e with
        | .forallE ..   => visitBinder #[] 0 e
        | .lam ..       => visitBinder #[] 0 e
        | .letE ..      => visitBinder #[] 0 e
        | .app f a      => visit f; visit a
        | .mdata _ b    => visit b
        | .proj _ _ b   => visit b
        | _             => return ()
  visit input |>.run

/-- Similar to `Expr.forEach`, but creates free variables whenever going inside of a binder. -/
def forEachExpr (e : Expr) (f : Expr → m Unit) : m Unit :=
  forEachExpr' e fun e => do
    f e
    return true

/-- Return true iff `x` is a metavariable with an anonymous user facing name. -/
private def shouldInferBinderName (x : Expr) : m Bool := do
  match x with
  | .mvar mvarId => return (← mvarId.getDecl).userName.isAnonymous
  | _ => return false

/--
  Auxiliary method for (temporarily) setting the user facing name of metavariables.
  Let `?m` be a metavariable in `isTarget.contains ?m`, and `?m` does not have a user facing name.
  Then, we try to find an application `f ... ?m` in `e`, and (temporarily) use the
  corresponding parameter name (with a fresh macro scope) as the user facing name for `?m`.
  This method returns all metavariables whose user facing name has been updated.
-/
def setMVarUserNamesAt (e : Expr) (isTarget : Array Expr) : MetaM (Array MVarId) := do
  let toReset ← IO.mkRef #[]
  forEachExpr (← instantiateMVars e) fun e => do
    if e.isApp then
      let args := e.getAppArgs
      for i in [:args.size] do
        let arg := args[i]!
        if arg.isMVar && isTarget.contains arg then
          let mvarId := arg.mvarId!
          if (← mvarId.getDecl).userName.isAnonymous then
            forallBoundedTelescope (← inferType e.getAppFn) (some (i+1)) fun xs _ => do
              if i < xs.size then
                let mvarId := arg.mvarId!
                let userName ← mkFreshUserName (← getFVarLocalDecl xs[i]!).userName
                toReset.modify (·.push mvarId)
                modifyMCtx fun mctx => mctx.setMVarUserNameTemporarily mvarId userName
  toReset.get

/--
  Remove user facing name for metavariables in `toReset`.
  This a low-level method for "undoing" the effect of `setMVarUserNamesAt`
-/
def resetMVarUserNames (toReset : Array MVarId) : MetaM Unit := do
  for mvarId in toReset do
    modifyMCtx fun mctx => mctx.setMVarUserNameTemporarily mvarId Name.anonymous

/--
  Similar to `mkForallFVars`, but tries to infer better binder names when `xs` contains metavariables.
  Let `?m` be a metavariable in `xs` s.t. `?m` does not have a user facing name.
  Then, we try to find an application `f ... ?m` in the other binder typer and `type`, and
  (temporarily) use the corresponding parameter name (with a fresh macro scope) as the user facing name for `?m`.
  The "renaming" is temporary.
-/
def mkForallFVars' (xs : Array Expr) (type : Expr) : MetaM Expr := do
  if (← xs.anyM shouldInferBinderName) then
    let setMVarsAt (e : Expr) : StateRefT (Array MVarId) MetaM Unit := do
      let mvarIds ← setMVarUserNamesAt e xs
      modify (· ++ mvarIds)
    let go : StateRefT (Array MVarId) MetaM Expr := do
      try
        for x in xs do
          setMVarsAt (← inferType x)
        setMVarsAt type
        mkForallFVars xs type
      finally
        resetMVarUserNames (← get)
    go |>.run' #[]
  else
    mkForallFVars xs type

end Lean.Meta
