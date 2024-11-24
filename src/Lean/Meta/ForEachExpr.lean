/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Util.MonadCache
import Lean.Meta.Basic

namespace Lean.Meta

variable {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]

/-- Given an expression `e = fun (x₁ : α₁) .. (xₙ : αₙ) => b`, runs `f` on each `αᵢ` and `b`. -/
def visitLambda (f : Expr → m Unit) (e : Expr) : m Unit := visit #[] e
  where visit (fvars : Array Expr) : Expr → m Unit
    | Expr.lam n d b c => do
      let d := d.instantiateRev fvars
      f d
      withLocalDecl n c d fun x =>
        visit (fvars.push x) b
    | e => do
      f <| e.instantiateRev fvars

/-- Given an expression `e =  (x₁ : α₁) → .. (xₙ : αₙ) → b`, runs `f` on each `αᵢ` and `b`. -/
def visitForall (f : Expr → m Unit) (e : Expr) : m Unit := visit #[] e
  where visit (fvars : Array Expr) : Expr → m Unit
    | Expr.forallE n d b c => do
      let d := d.instantiateRev fvars
      f d
      withLocalDecl n c d fun x =>
        visit (fvars.push x) b
    | e => do
      f <| e.instantiateRev fvars

/-- Given a sequence of let binders `let (x₁ : α₁ := v₁) ... in b`, runs `f` on each `αᵢ`, `vᵢ` and `b`. -/
def visitLet (f : Expr → m Unit) (e : Expr) : m Unit := visit #[] e
  where visit (fvars : Array Expr) : Expr → m Unit
    | Expr.letE n d v b _ => do
      let d := d.instantiateRev fvars
      let v := v.instantiateRev fvars
      f d
      f v
      withLetDecl n d v fun x =>
        visit (fvars.push x) b
    | e => do
      f <| e.instantiateRev fvars

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
    checkCache e fun _ => do
      if (← liftM (fn e)) then
        match e with
        | .forallE ..   => visitForall visit e
        | .lam ..       => visitLambda visit e
        | .letE ..      => visitLet visit e
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
      for h : i in [:args.size] do
        let arg := args[i]
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
