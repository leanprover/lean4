/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic

namespace Lean

inductive TransformStep where
  /-- Return expression without visiting any subexpressions. -/
  | done (e : Expr)
  /--
  Visit expression (which should be different from current expression) instead.
  The new expression `e` is passed to `pre` again.
  -/
  | visit (e : Expr)
  /--
  Continue transformation with the given expression (defaults to current expression).
  For `pre`, this means visiting the children of the expression.
  For `post`, this is equivalent to returning `done`. -/
  | continue (e? : Option Expr := none)
  deriving Inhabited, Repr

namespace Core

/--
  Transform the expression `input` using `pre` and `post`.
  - First `pre` is invoked with the current expression and recursion is continued according to the `TransformStep` result.
    In all cases, the expression contained in the result, if any, must be definitionally equal to the current expression.
  - After recursion, if any, `post` is invoked on the resulting expression.

  The term `s` in both `pre s` and `post s` may contain loose bound variables. So, this method is not appropriate for
  if one needs to apply operations (e.g., `whnf`, `inferType`) that do not handle loose bound variables.
  Consider using `Meta.transform` to avoid loose bound variables.

  This method is useful for applying transformations such as beta-reduction and delta-reduction.
-/
partial def transform {m} [Monad m] [MonadLiftT CoreM m] [MonadControlT CoreM m]
    (input : Expr)
    (pre   : Expr → m TransformStep := fun _ => return .continue)
    (post  : Expr → m TransformStep := fun e => return .done e)
    : m Expr :=
  let _ : STWorld IO.RealWorld m := ⟨⟩
  let _ : MonadLiftT (ST IO.RealWorld) m := { monadLift := fun x => liftM (m := CoreM) (liftM (m := ST IO.RealWorld) x) }
  let rec visit (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
    checkCache { val := e : ExprStructEq } fun _ => Core.withIncRecDepth do
      let rec visitPost (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match (← post e) with
        | .done e      => pure e
        | .visit e     => visit e
        | .continue e? => pure (e?.getD e)
      match (← pre e) with
      | .done e  => pure e
      | .visit e => visitPost (← visit e)
      | .continue e? =>
        let e := e?.getD e
        match e with
        | .forallE _ d b _ => visitPost (e.updateForallE! (← visit d) (← visit b))
        | .lam _ d b _     => visitPost (e.updateLambdaE! (← visit d) (← visit b))
        | .letE _ t v b _  => visitPost (e.updateLetE! (← visit t) (← visit v) (← visit b))
        | .app ..          => e.withApp fun f args => do visitPost (mkAppN (← visit f) (← args.mapM visit))
        | .mdata _ b       => visitPost (e.updateMData! (← visit b))
        | .proj _ _ b      => visitPost (e.updateProj! (← visit b))
        | _                => visitPost e
  visit input |>.run

def betaReduce (e : Expr) : CoreM Expr :=
  transform e (pre := fun e => return if e.isHeadBetaTarget then .visit e.headBeta else .continue)

end Core

namespace Meta

/--
Similar to `Meta.transform`, but allows the use of a pre-existing cache.

Warnings:
- For the cache to be valid, it must always use the same `pre` and `post` functions.
- It is important that there are no other references to `cache` when it is passed to
  `transformWithCache`, to avoid unnecessary copying of the hash map.
-/
@[inline]
partial def transformWithCache {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (input : Expr)
    (cache : Std.HashMap ExprStructEq Expr)
    (pre   : Expr → m TransformStep := fun _ => return .continue)
    (post  : Expr → m TransformStep := fun e => return .done e)
    (usedLetOnly := false)
    (skipConstInApp := false)
    : m (Expr × Std.HashMap ExprStructEq Expr) :=
  let _ : STWorld IO.RealWorld m := ⟨⟩
  let _ : MonadLiftT (ST IO.RealWorld) m := { monadLift := fun x => liftM (m := MetaM) (liftM (m := ST IO.RealWorld) x) }
  let rec visit (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
    checkCache { val := e : ExprStructEq } fun _ => Meta.withIncRecDepth do
      let rec visitPost (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match (← post e) with
        | .done e      => pure e
        | .visit e     => visit e
        | .continue e? => pure (e?.getD e)
      let rec visitLambda (fvars : Array Expr) (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match e with
        | .lam n d b c =>
          withLocalDecl n c (← visit (d.instantiateRev fvars)) fun x =>
            visitLambda (fvars.push x) b
        | e => visitPost (← mkLambdaFVars (usedLetOnly := usedLetOnly) fvars (← visit (e.instantiateRev fvars)))
      let rec visitForall (fvars : Array Expr) (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match e with
        | .forallE n d b c =>
          withLocalDecl n c (← visit (d.instantiateRev fvars)) fun x =>
            visitForall (fvars.push x) b
        | e => visitPost (← mkForallFVars (usedLetOnly := usedLetOnly) fvars (← visit (e.instantiateRev fvars)))
      let rec visitLet (fvars : Array Expr) (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match e with
        | .letE n t v b nondep =>
          withLetDecl n (← visit (t.instantiateRev fvars)) (← visit (v.instantiateRev fvars)) (nondep := nondep) fun x =>
            visitLet (fvars.push x) b
        | e => visitPost (← mkLetFVars (usedLetOnly := usedLetOnly) (generalizeNondepLet := false) fvars (← visit (e.instantiateRev fvars)))
      let visitApp (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
        e.withApp fun f args => do
          if skipConstInApp && f.isConst then
            visitPost (mkAppN f (← args.mapM visit))
          else
            visitPost (mkAppN (← visit f) (← args.mapM visit))
      match (← pre e) with
      | .done e  => pure e
      | .visit e => visit e
      | .continue e? =>
        let e := e?.getD e
        match e with
        | .forallE ..    => visitForall #[] e
        | .lam ..        => visitLambda #[] e
        | .letE ..       => visitLet #[] e
        | .app ..        => visitApp e
        | .mdata _ b     => visitPost (e.updateMData! (← visit b))
        | .proj _ _ b    => visitPost (e.updateProj! (← visit b))
        | _              => visitPost e
  StateRefT'.run (visit input) cache

/--
Similar to `Core.transform`, but terms provided to `pre` and `post` do not contain loose bound variables.
So, it is safe to use any `MetaM` method at `pre` and `post`.

Warning: `pre` and `post` should not depend on variables in the local context introduced by `transform`.
This is in order to allow aggressive caching.

If `skipConstInApp := true`, then for an expression `mkAppN (.const f) args`, the subexpression
`.const f` is not visited again. Put differently: every `.const f` is visited once, with its
arguments if present, on its own otherwise.
-/
def transform {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (input : Expr)
    (pre   : Expr → m TransformStep := fun _ => return .continue)
    (post  : Expr → m TransformStep := fun e => return .done e)
    (usedLetOnly := false)
    (skipConstInApp := false)
    : m Expr := do
  let (e, _) ← transformWithCache input {} pre post usedLetOnly skipConstInApp
  return e

-- TODO: add options to distinguish zeta and zetaDelta reduction
def zetaReduce (e : Expr) : MetaM Expr := do
  let pre (e : Expr) : MetaM TransformStep := do
    let .fvar fvarId := e | return .continue
    let some localDecl := (← getLCtx).find? fvarId | return .done e
    let some value := localDecl.value? | return .done e
    return .visit (← instantiateMVars value)
  transform e (pre := pre) (usedLetOnly := true)

/--
Zeta reduces only the provided fvars, beta reducing the substitutions.
-/
def zetaDeltaFVars (e : Expr) (fvars : Array FVarId) : MetaM Expr :=
  let unfold? (fvarId : FVarId) : MetaM (Option Expr) := do
    if fvars.contains fvarId then
      fvarId.getValue?
    else
      return none
  let pre (e : Expr) : MetaM TransformStep := do
    let .fvar fvarId := e.getAppFn | return .continue
    let some val ← unfold? fvarId | return .continue
    return .visit <| (← instantiateMVars val).beta e.getAppArgs
  transform e (pre := pre)

/-- Unfold definitions and theorems in `e` that are not in the current environment, but are in `biggerEnv`. -/
def unfoldDeclsFrom (biggerEnv : Environment) (e : Expr) : CoreM Expr := do
  withoutModifyingEnv do
    let env ← getEnv
    setEnv biggerEnv -- `e` has declarations from `biggerEnv` that are not in `env`
    let pre (e : Expr) : CoreM TransformStep := do
      let .const declName us := e | return .continue
      if env.contains declName then
        return .done e
      let some info := biggerEnv.find? declName | return .done e
      if info.hasValue then
        return .visit (← instantiateValueLevelParams info us)
      else
        return .done e
    Core.transform e (pre := pre)

def eraseInaccessibleAnnotations (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun e => return .done <| if let some e := inaccessible? e then e else e)

def erasePatternRefAnnotations (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun e => return .done <| if let some (_, e) := patternWithRef? e then e else e)

end Lean.Meta
