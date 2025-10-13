/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.FunInfo
import Init.Data.Range.Polymorphic.Iterators
public section
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
Recursively transforms `input` using `pre` and `post` callbacks.

For each subexpression:
1. `pre` is invoked first; recursion continues according to the `TransformStep` result.
2. After recursion (if any), `post` is invoked on the resulting expression.

The expressions passed to `pre` and `post` may contain loose bound variables.
Use `Meta.transform` instead if you need operations like `whnf` or `inferType`
that require expressions without loose bound variables.

Results are cached using pointer equality (`ExprStructEq`), so structurally
identical subexpressions are transformed only once.
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

/-- Applies beta reduction to all beta-reducible subexpressions in `e`. -/
def betaReduce (e : Expr) : CoreM Expr :=
  transform e (pre := fun e => return if e.isHeadBetaTarget then .visit e.headBeta else .continue)

end Core

namespace Meta

/--
Like `Meta.transform`, but accepts and returns a cache for reuse across multiple calls.

Parameters:
- `usedLetOnly`: when true, `mkLambdaFVars`/`mkForallFVars`/`mkLetFVars` only abstract
  over variables that are actually used in the body.
- `skipConstInApp`: when true, constant heads in applications are not visited separately.
- `skipInstances`: when true, instance arguments (determined via `getFunInfo`) are not visited.

The `skipInstances` flag is used by `dsimp` to avoid rewriting instances.

**Warnings:**
- The cache is only valid when using the same `pre` and `post` functions.
- Ensure there are no other references to `cache` to avoid unnecessary hash map copying.
-/
@[inline]
partial def transformWithCache {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (input : Expr)
    (cache : Std.HashMap ExprStructEq Expr)
    (pre   : Expr → m TransformStep := fun _ => return .continue)
    (post  : Expr → m TransformStep := fun e => return .done e)
    (usedLetOnly := false)
    (skipConstInApp := false)
    (skipInstances := false)
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
        let f ← if skipConstInApp && f.isConst then pure f else visit f
        if skipInstances then
          let infos := (← getFunInfoNArgs f args.size).paramInfo
          let mut args := args.toVector
          for h : i in *...args.size do
            let arg := args[i]
            if h : i < infos.size then
              let info := infos[i]
              if skipInstances && info.isInstance then
                continue
              args := args.set i (← visit arg)
            else
              args := args.set i (← visit arg)
          visitPost (mkAppN f args.toArray)
        else
          visitPost (mkAppN f (← args.mapM visit))
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

/--
Replaces all free variables in `e` that have let-values with their values.
The substitution is applied recursively to the values themselves.
-/
-- TODO: add options to distinguish zeta and zetaDelta reduction
def zetaReduce (e : Expr) : MetaM Expr := do
  let pre (e : Expr) : MetaM TransformStep := do
    let .fvar fvarId := e | return .continue
    let some localDecl := (← getLCtx).find? fvarId | return .done e
    let some value := localDecl.value? | return .done e
    return .visit (← instantiateMVars value)
  transform e (pre := pre) (usedLetOnly := true)

/--
Zeta-reduces only the specified free variables, applying beta reduction after substitution.
For example, if `x` has value `fun y => y + 1` and appears as `x 2`, the result is `2 + 1`.
-/
def zetaDeltaFVars (e : Expr) (fvars : Array FVarId) (allowNondep : Bool := false) : MetaM Expr :=
  let unfold? (fvarId : FVarId) : MetaM (Option Expr) := do
    if fvars.contains fvarId then
      fvarId.getValue? (allowNondep := allowNondep)
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
    -- There might have been nested proof abstractions, which yield private helper theorems, so
    -- make sure we can find them. They will later be re-abstracted again.
    let biggerEnv := biggerEnv.setExporting false
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

/--
Unfolds theorems that are applied to `f x₁ .. xₙ` where `f` is in `fnNames` and
`n ≤ numSectionVars` (i.e., an unsaturated application of `f`).

This is used to undo proof abstraction for termination checking, as otherwise the bare
occurrence of the recursive function prevents termination checking from succeeding.

Usually, the argument is just `f` (the constant), arising from `mkAuxTheorem` abstracting over the
aux decl representing `f`. If the mutual function is defined within the scope of `variable` commands,
it is `f x y` where `x y` are the variables in scope, so we use the `numSectionVars` to recognize that
while avoiding to unfold theorems applied to saturated applications of `f`.

This unfolds from the private environment. The resulting definitions are (usually) not
exposed anyways.
-/
def unfoldIfArgIsAppOf (fnNames : Array Name) (numSectionVars : Nat) (e : Expr) : CoreM Expr := withoutExporting do
  let env ← getEnv
  -- Unfold abstracted proofs
  Core.transform e
    (pre := fun e => e.withAppRev fun f revArgs => do
      if f.isConst then
        /-
        How do we avoid unfolding declarations where the user happened to
        have called with the recursive function as an unsaturated argument?
        Such cases are not caught by the following check,
        because such explicit recursive calls would always have a
        isRecApp mdata wrapper around.
        This is arguably somewhat fragile, but it works for now.
        Alternatives if this breaks:
         * Keep a local env extension to reliably recognize abstracted proofs
         * Avoid abstracting over implementation detail applications
        (The code below is restricted to theorems, as otherwise it would unfold
        matchers, which can also abstract over recursive calls without an `mdata` wrapper, #2102.)
        -/
        if revArgs.any isInterestingArg then
          if let some info@(.thmInfo _) := env.find? f.constName! then
            return .visit <| (← instantiateValueLevelParams info f.constLevels!).betaRev revArgs
      return .continue)
  where
    isInterestingArg (a : Expr) : Bool := a.withApp fun af axs =>
      af.isConst && fnNames.any fun f => af.constName! == f && axs.size ≤ numSectionVars


/-- Removes all `inaccessible` annotations from `e`. -/
def eraseInaccessibleAnnotations (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun e => return .done <| if let some e := inaccessible? e then e else e)

/-- Removes all `patternWithRef` annotations from `e`. -/
def erasePatternRefAnnotations (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun e => return .done <| if let some (_, e) := patternWithRef? e then e else e)

end Lean.Meta
