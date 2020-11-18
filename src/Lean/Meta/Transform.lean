/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic

namespace Lean.Meta

inductive TransformStep
  | done  (e : Expr)
  | visit (e : Expr)

partial def transform {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (input : Expr)
    (pre   : Expr → m TransformStep := fun e => return TransformStep.visit e)
    (post  : Expr → m TransformStep := fun e => return TransformStep.done e)
    : m Expr :=
  let inst : STWorld IO.RealWorld m := ⟨⟩
  let inst : MonadLiftT (ST IO.RealWorld) m := { monadLift := fun x => liftM (m := MetaM) (liftM (m := ST IO.RealWorld) x) }
  let rec visit (e : Expr) : MonadCacheT Expr Expr m Expr :=
    checkCache e fun e => Meta.withIncRecDepth do
      let rec visitPost (e : Expr) : MonadCacheT Expr Expr m Expr := do
        match (← post e) with
        | TransformStep.done e  => pure e
        | TransformStep.visit e => visit e
      let rec visitLambda (fvars : Array Expr) (e : Expr) : MonadCacheT Expr Expr m Expr := do
        match e with
        | Expr.lam n d b c =>
          withLocalDecl n c.binderInfo (← visit (d.instantiateRev fvars)) fun x =>
            visitLambda (fvars.push x) b
        | e => visitPost (← mkLambdaFVars fvars (← visit (e.instantiateRev fvars)))
      let rec visitForall (fvars : Array Expr) (e : Expr) : MonadCacheT Expr Expr m Expr := do
        match e with
        | Expr.forallE n d b c =>
          withLocalDecl n c.binderInfo (← visit (d.instantiateRev fvars)) fun x =>
            visitForall (fvars.push x) b
        | e => visitPost (← mkForallFVars fvars (← visit (e.instantiateRev fvars)))
      let rec visitLet (fvars : Array Expr) (e : Expr) : MonadCacheT Expr Expr m Expr := do
        match e with
        | Expr.letE n t v b _ =>
          withLetDecl n (← visit (t.instantiateRev fvars)) (← visit (v.instantiateRev fvars)) fun x =>
            visitLet (fvars.push x) b
        | e => visitPost (← mkLetFVars fvars (← visit (e.instantiateRev fvars)))
      let visitApp (e : Expr) : MonadCacheT Expr Expr m Expr :=
        e.withApp fun f args => do
          visitPost (mkAppN (← visit f) (← args.mapM visit))
      match (← pre e) with
      | TransformStep.done e  => pure e
      | TransformStep.visit e => match e with
        | Expr.forallE ..    => visitLambda #[] e
        | Expr.lam ..        => visitForall #[] e
        | Expr.letE ..       => visitLet #[] e
        | Expr.app ..        => visitApp e
        | Expr.mdata _ b _   => visitPost (e.updateMData! (← visit b))
        | Expr.proj _ _ b _  => visitPost (e.updateProj! (← visit b))
        | _                  => visitPost e
  visit input $.run

end Lean.Meta
