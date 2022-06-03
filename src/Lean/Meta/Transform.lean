/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, E.W.Ayers
-/
import Lean.Meta.Basic

namespace Lean

inductive TransformStep where
  | done  (e : Expr)
  | visit (e : Expr)


/-- Given `e = fn a₁ ... aₙ`, runs `f` on `fn` and each of the arguments `aᵢ` and
makes a new function application with the results. -/
def Expr.traverseApp {M} [Monad M]
  (f : Expr → M Expr) (e : Expr) : M Expr :=
  e.withApp fun fn args => (pure mkAppN) <*> (f fn) <*> (args.mapM f)

namespace Core

/--
  Tranform the expression `input` using `pre` and `post`.
  - `pre s` is invoked before visiting the children of subterm 's'. If the result is `TransformStep.visit sNew`, then
     `sNew` is traversed by transform. If the result is `TransformStep.done sNew`, then `s` is just replaced with `sNew`.
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
  let _ : STWorld IO.RealWorld m := ⟨⟩
  let _ : MonadLiftT (ST IO.RealWorld) m := { monadLift := fun x => liftM (m := CoreM) (liftM (m := ST IO.RealWorld) x) }
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

variable {M} [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M] [MonadOptions M]

def usedLetOnly : M Bool := getBoolOption `visit.usedLetOnly false

/-- Given an expression `fun (x₁ : α₁) ... (xₙ : αₙ) => b`, will run
`f` on each of the variable types `αᵢ` and `b` with the correct MetaM context,
replacing each expression with the output of `f` and creating a new lambda.
(that is, correctly instantiating bound variables and repackaging them after)  -/
def traverseLambda
  (f : Expr → M Expr) (e : Expr) : M Expr := visit #[] e
  where visit (fvars : Array Expr) : Expr  → M Expr
    | (Expr.lam n d b c) => do withLocalDecl n c.binderInfo (← f (d.instantiateRev fvars)) fun x => visit (fvars.push x) b
    | e => do mkLambdaFVars (usedLetOnly := ← usedLetOnly) fvars (← f (e.instantiateRev fvars))

/-- Given an expression ` (x₁ : α₁) → ... → (xₙ : αₙ) → b`, will run
`f` on each of the variable types `αᵢ` and `b` with the correct MetaM context,
replacing the expression with the output of `f` and creating a new forall expression.
(that is, correctly instantiating bound variables and repackaging them after)  -/
def traverseForall
  (f : Expr → M Expr) (e : Expr) : M Expr := visit #[] e
  where visit fvars : Expr → M Expr
    | (Expr.forallE n d b c) => do withLocalDecl n c.binderInfo (← f (d.instantiateRev fvars)) fun x => visit (fvars.push x) b
    | e   => do mkForallFVars (usedLetOnly := ←usedLetOnly) fvars (← f (e.instantiateRev fvars))

/-- Similar to traverseLambda and traverseForall but with let binders.  -/
def traverseLet
  (f : Expr → M Expr) (e : Expr) : M Expr := visit #[] e
  where visit fvars
    | Expr.letE n t v b _ => do
      withLetDecl n (← f (t.instantiateRev fvars)) (← f (v.instantiateRev fvars)) fun x =>
        visit (fvars.push x) b
    | e => do mkLetFVars (usedLetOnly := ←usedLetOnly) fvars (← f (e.instantiateRev fvars))

/-- Maps `f` on each child of the given expression.

Applications, foralls, lambdas and let binders are bundled (as they are bundled in `Expr.traverseApp`, `traverseForall`, ...).
So `traverseChildren f e` where ``e = `(fn a₁ ... aₙ)`` will return
``(← f `(fn)) (← f `(a₁)) ... (← f `(aₙ))`` rather than ``(← f `(fn a₁ ... aₙ₋₁)) (← f `(aₙ))``
 -/
def traverseChildren (f : Expr → M Expr) (e: Expr) : M Expr := do
  match e with
  | Expr.forallE ..    => traverseForall f e
  | Expr.lam ..        => traverseLambda f e
  | Expr.letE ..       => traverseLet f e
  | Expr.app ..        => Expr.traverseApp f e
  | Expr.mdata _ b _   => return e.updateMData! (← f b)
  | Expr.proj _ _ b _  => return e.updateProj! (← f b)
  | _                  => return e

/--
  Similar to `Core.transform`, but terms provided to `pre` and `post` do not contain loose bound variables.
  So, it is safe to use any `MetaM` method at `pre` and `post`. -/
partial def transform {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadTrace m] [MonadRef m] [MonadOptions m] [MonadWithOptions m] [AddMessageContext m]
    (input : Expr)
    (pre   : Expr → m TransformStep := fun e => return TransformStep.visit e)
    (post  : Expr → m TransformStep := fun e => return TransformStep.done e)
    (usedLetOnly := false)
    : m Expr := do
  let _ : STWorld IO.RealWorld m := ⟨⟩
  let _ : MonadLiftT (ST IO.RealWorld) m := { monadLift := fun x => liftM (m := MetaM) (liftM (m := ST IO.RealWorld) x) }
  let rec visit (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
    checkCache { val := e : ExprStructEq } fun _ => Meta.withIncRecDepth do
      match (← pre e) with
      | TransformStep.done e  => pure e
      | TransformStep.visit e =>
        let e ← traverseChildren visit e
        match (← post e) with
        | TransformStep.done e => pure e
        | TransformStep.visit e => visit e
  withOptions (fun o => o.setBool `visit.usedLetOnly usedLetOnly)
    (visit input |>.run)

def zetaReduce (e : Expr) : MetaM Expr := do
  let pre (e : Expr) : MetaM TransformStep := do
    match e with
    | Expr.fvar fvarId _ =>
      match (← getLCtx).find? fvarId with
      | none => return TransformStep.done e
      | some localDecl =>
        if let some value := localDecl.value? then
          return TransformStep.visit value
        else
          return TransformStep.done e
    | e => return TransformStep.visit e
  transform e (pre := pre) (usedLetOnly := true)

/-- Unfold definitions and theorems in `e` that are not in the current environment, but are in `biggerEnv`. -/
def unfoldDeclsFrom (biggerEnv : Environment) (e : Expr) : CoreM Expr := do
  withoutModifyingEnv do
    let env ← getEnv
    setEnv biggerEnv -- `e` has declarations from `biggerEnv` that are not in `env`
    let pre (e : Expr) : CoreM TransformStep := do
      match e with
      | Expr.const declName us .. =>
        if env.contains declName then
          return TransformStep.done e
        else if let some info := biggerEnv.find? declName then
          if info.hasValue then
            return TransformStep.visit (← instantiateValueLevelParams info us)
          else
            return TransformStep.done e
        else
          return TransformStep.done e
      | _ => return TransformStep.visit e
    Core.transform e (pre := pre)

def eraseInaccessibleAnnotations (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun e => return TransformStep.done <| if let some e := inaccessible? e then e else e)

def erasePatternRefAnnotations (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun e => return TransformStep.done <| if let some (_, e) := patternWithRef? e then e else e)

end Meta
end Lean
