/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic

namespace Lean

inductive TransformStep where
  | done  (e : Expr)
  | visit (e : Expr)

namespace Core

/--
  Tranform the expression `input` using `pre` and `post`.
  - `pre s` is invoked before visiting the children of subterm 's'. If the result is `TransformStep.visit sNew`, then
     `sNew` is traversed by transform. If the result is `TransformStep.visit sNew`, then `s` is just replaced with `sNew`.
     In both cases, `sNew` must be definitionally equal to `s`
  - `post s` is invoked after visiting the children of subterm `s`.

  The term `s` in both `pre s` and `post s` may contain loose bound variables. So, this method is not appropriate for
  if one needs to apply operations (e.g., `whnf`, `inferType`) that do not handle loose bound variables.
  Consider using `Meta.transform` to avoid loose bound variables.

  This method is useful for applying transformations such as beta-reduction and delta-reduction.
-/
partial def transform {m} [Monad m] [MonadLiftT CoreM m] [MonadControlT CoreM m]
    (input : Expr)
    (pre   : Expr → m TransformStep := fun e => return TransformStep.visit e)
    (post  : Expr → m TransformStep := fun e => return TransformStep.done e)
    : m Expr :=
  let inst : STWorld IO.RealWorld m := ⟨⟩
  let inst : MonadLiftT (ST IO.RealWorld) m := { monadLift := fun x => liftM (m := CoreM) (liftM (m := ST IO.RealWorld) x) }
  let rec visit (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
    checkCache { val := e : ExprStructEq } fun _ => Core.withIncRecDepth do
      let rec visitPost (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match (← post e) with
        | TransformStep.done e  => pure e
        | TransformStep.visit e => visit e
      match (← pre e) with
      | TransformStep.done e  => pure e
      | TransformStep.visit e => match e with
        | Expr.forallE _ d b _ => visitPost (e.updateForallE! (← visit d) (← visit b))
        | Expr.lam _ d b _     => visitPost (e.updateLambdaE! (← visit d) (← visit b))
        | Expr.letE _ t v b _  => visitPost (e.updateLet! (← visit t) (← visit v) (← visit b))
        | Expr.app ..          => e.withApp fun f args => do visitPost (mkAppN (← visit f) (← args.mapM visit))
        | Expr.mdata _ b _     => visitPost (e.updateMData! (← visit b))
        | Expr.proj _ _ b _    => visitPost (e.updateProj! (← visit b))
        | _                    => visitPost e
  visit input |>.run

def betaReduce (e : Expr) : CoreM Expr :=
  transform e (pre := fun e => return TransformStep.visit e.headBeta)

end Core

namespace Meta

/--
  Similar to `Core.transform`, but terms provided to `pre` and `post` do not contain loose bound variables.
  So, it is safe to use any `MetaM` method at `pre` and `post`. -/
partial def transform {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (input : Expr)
    (pre   : Expr → m TransformStep := fun e => return TransformStep.visit e)
    (post  : Expr → m TransformStep := fun e => return TransformStep.done e)
    : m Expr :=
  let inst : STWorld IO.RealWorld m := ⟨⟩
  let inst : MonadLiftT (ST IO.RealWorld) m := { monadLift := fun x => liftM (m := MetaM) (liftM (m := ST IO.RealWorld) x) }
  let rec visit (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
    checkCache { val := e : ExprStructEq } fun _ => Meta.withIncRecDepth do
      let rec visitPost (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match (← post e) with
        | TransformStep.done e  => pure e
        | TransformStep.visit e => visit e
      let rec visitLambda (fvars : Array Expr) (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match e with
        | Expr.lam n d b c =>
          withLocalDecl n c.binderInfo (← visit (d.instantiateRev fvars)) fun x =>
            visitLambda (fvars.push x) b
        | e => visitPost (← mkLambdaFVars fvars (← visit (e.instantiateRev fvars)))
      let rec visitForall (fvars : Array Expr) (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match e with
        | Expr.forallE n d b c =>
          withLocalDecl n c.binderInfo (← visit (d.instantiateRev fvars)) fun x =>
            visitForall (fvars.push x) b
        | e => visitPost (← mkForallFVars fvars (← visit (e.instantiateRev fvars)))
      let rec visitLet (fvars : Array Expr) (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match e with
        | Expr.letE n t v b _ =>
          withLetDecl n (← visit (t.instantiateRev fvars)) (← visit (v.instantiateRev fvars)) fun x =>
            visitLet (fvars.push x) b
        | e => visitPost (← mkLetFVars fvars (← visit (e.instantiateRev fvars)))
      let visitApp (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
        e.withApp fun f args => do
          visitPost (mkAppN (← visit f) (← args.mapM visit))
      match (← pre e) with
      | TransformStep.done e  => pure e
      | TransformStep.visit e => match e with
        | Expr.forallE ..    => visitForall #[] e
        | Expr.lam ..        => visitLambda #[] e
        | Expr.letE ..       => visitLet #[] e
        | Expr.app ..        => visitApp e
        | Expr.mdata _ b _   => visitPost (e.updateMData! (← visit b))
        | Expr.proj _ _ b _  => visitPost (e.updateProj! (← visit b))
        | _                  => visitPost e
  visit input |>.run

def zetaReduce (e : Expr) : MetaM Expr := do
  let lctx ← getLCtx
  let pre (e : Expr) : CoreM TransformStep := do
    match e with
    | Expr.fvar fvarId _ =>
      match lctx.find? fvarId with
      | none => return TransformStep.done e
      | some localDecl =>
        if let some value := localDecl.value? then
          return TransformStep.visit value
        else
          return TransformStep.done e
    | e => if e.hasFVar then return TransformStep.visit e else return TransformStep.done e
  liftM (m := CoreM) <| Core.transform e (pre := pre)

end Meta
end Lean
