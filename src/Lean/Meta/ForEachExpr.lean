/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.SubExpr
import Lean.Util.MonadCache
import Lean.Meta.Basic

open Lean.SubExpr

namespace Lean

variable {m : Type → Type}
/-- Convert a traversal function to a form without the `Pos` argument. -/
private def forgetPos (t : (Pos → α → m β) → (Pos → α → m β)) (visit : α → m β) (e : α) : m β :=
  t (fun _ => visit) Pos.root e

/-- Visits all the immediate child subexpressions of the given expression.
Includes a `Pos` parameter that is used to track position in the subexpression.

Does not instantiate bound variables if the subexpression is below a binder.
For that, use `Lean.Meta.visitChildrenWithPos`.
-/
def Expr.visitChildrenWithPos [Applicative m]
    (visit : Pos → Expr → m Unit) (p : Pos) : Expr → m Unit
  | Expr.proj _ _ e      => visit p.pushProj e
  | Expr.mdata _ b       => Expr.visitChildrenWithPos visit p b
  | Expr.app f a         => visit p.pushAppFn f *> visit p.pushAppArg a
  | Expr.lam _ t b _     => visit p.pushBindingDomain t *> visit p.pushBindingBody b
  | Expr.forallE _ t b _ => visit p.pushBindingDomain t *> visit p.pushBindingBody b
  | Expr.letE _ t v b _  => visit p.pushLetVarType t *> visit p.pushLetValue v *> visit p.pushLetBody b
  | _                    => pure ()

/-- Visits all the immediate child subexpressions of the given expression.

Does not instantiate bound variables if the subexpression is below a binder.
For that, use `Lean.Meta.visitChildren`.-/
def Expr.visitChildren [Applicative m] (visit : Expr → m Unit) : Expr → m Unit :=
  forgetPos Expr.visitChildrenWithPos visit

/-- Depth-first iterates over the subexpressions of the given expression.
If `f` returns `false`, deeper subexpressions will not be visited.

Does not instantiate bound variables if the subexpression is below a binder.
For that, use `Lean.Meta.forEach'`.
-/
partial def Expr.forEach' [Monad m] (f : Expr → m Bool) (e : Expr) : m Unit := do
  if (← f e) then Expr.visitChildren (Expr.forEach' f) e else return ()

namespace Meta

variable [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
open Lean.SubExpr

def visitLambdaWithPos (f : Pos → Expr → m Unit) (p : Pos) (e : Expr) : m Unit := visit #[] p e
  where visit (fvars : Array Expr) (p : Pos) : Expr → m Unit
    | Expr.lam n d b c => do
      let d := d.instantiateRev fvars
      f p.pushBindingDomain d
      withLocalDecl n c d fun x =>
        visit (fvars.push x) p.pushBindingBody b
    | e => do
      f p <| e.instantiateRev fvars

def visitForallWithPos (f : Pos → Expr → m Unit) (p : Pos) (e : Expr) : m Unit := visit #[] p e
  where visit (fvars : Array Expr) (p : Pos) : Expr → m Unit
    | Expr.forallE n d b c => do
      let d := d.instantiateRev fvars
      f p.pushBindingDomain d
      withLocalDecl n c d fun x =>
        visit (fvars.push x) p.pushBindingBody b
    | e => do
      f p <| e.instantiateRev fvars

def visitLetWithPos (f : Pos → Expr → m Unit) (p : Pos) (e : Expr) : m Unit := visit #[] p e
  where visit (fvars : Array Expr) (p : Pos) : Expr → m Unit
    | Expr.letE n d v b _ => do
      let d := d.instantiateRev fvars
      let v := v.instantiateRev fvars
      f p.pushLetVarType d
      f p.pushLetValue v
      withLetDecl n d v fun x =>
        visit (fvars.push x) p.pushLetBody b
    | e => do
      f p <| e.instantiateRev fvars

/-- Given an expression `e = fun (x₁ : α₁) .. (xₙ : αₙ) => b`, runs `f` on each `αᵢ` and `b`. -/
def visitLambda (f : Expr → m Unit) (e : Expr) := forgetPos visitLambdaWithPos f e

/-- Given an expression `e =  (x₁ : α₁) → .. (xₙ : αₙ) → b`, runs `f` on each `αᵢ` and `b`. -/
def visitForall (f : Expr → m Unit) (e : Expr) := forgetPos visitForallWithPos f e

/-- Given a sequence of let binders `let (x₁ : α₁ := v₁) ... in b`, runs `f` on each `αᵢ`, `vᵢ` and `b`. -/
def visitLet (f : Expr → m Unit) (e : Expr) := forgetPos visitLetWithPos f e

/-- Visits all the immediate child subexpressions of the given expression.
Includes a `Pos` parameter that is used to track position in the subexpression.

Instantiates bound variables if the subexpression is below a binder.
For that, use `Lean.Meta.visitChildrenWithPos`.
-/
def visitChildrenWithPos (visit : Pos → Expr → m Unit) (p : Pos) (e : Expr) :=
  match e with
  | .forallE .. => visitForallWithPos visit p e
  | .lam ..     => visitLambdaWithPos visit p e
  | .letE ..    => visitLetWithPos visit p e
  | .app ..     => Expr.visitAppWithPos visit p e
  | .mdata _ b  => visitChildrenWithPos visit p b
  | .proj _ _ b => visit p.pushProj b
  | _ => pure ()

/-- Visits the immediate child subexpressions of the given expression.
Instantiates bound variables is the subexpression is below a binder.
-/
def visitChildren (visit : Expr → m Unit) (e : Expr) :=
  forgetPos visitChildrenWithPos visit e

/-- Version of `forEachExpr'` with additional subexpr pos information.
If the inner function returns `false`, deeper subexpressions will not be visited. -/
partial def forEachExprWithPos' (fn : Pos → Expr → m Bool) (p : Pos) (e : Expr) : m Unit := do
  if ← fn p e then visitChildrenWithPos (forEachExprWithPos' fn) p e

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

end Meta
end Lean
