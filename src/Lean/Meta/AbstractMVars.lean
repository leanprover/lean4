/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
import Lean.Util.CollectLevelMVars
import Lean.Util.CollectMVars
import Lean.Meta.ForEachExpr
import Lean.Meta.Transform

/-!
# Abstracting metavariables from expressions

This module provides `abstractMVars`, which takes an expression `e` and returns a lambda function
with parameters for each free metavariable. Using `lambdaMetaTelescope`, the result can
be instantiated with fresh metavariables.

One application is packaging up an expression for transport to an incompatible metacontext.
Another is to systematically copy an expression with fresh metavariables.

Not every metavariable is abstracted. Any metavariables that are depended on by free variables
that are depended on by `e` are fixed.
-/

namespace Lean.Meta
namespace AbstractMVars

structure Context where
  /-- Whether or not to abstract level mvars. -/
  abstractLevels : Bool
  /-- The binder info to use for the abstracted mvars. -/
  binderInfo     : BinderInfo

structure State where
  ngen           : NameGenerator
  /-- Local context, updated with declarations for abstracted metavariables. -/
  lctx           : LocalContext
  mctx           : MetavarContext
  nextParamIdx   : Nat := 1
  /-- Level parameter names for abstracted level metavariables. -/
  paramNames     : Array Name := #[]
  /-- Level metavariables that were abstracted, corresponding to `paramNames`. -/
  lmvars         : Array Level := #[]
  /-- The `fvars` that were added to `lctx`. -/
  fvars          : Array Expr := #[]
  /-- Values that can substitute for the corresponding `fvars` to get the original expression.
  These are currently the abstracted metavariables.
  If `abstractMVars` handles delayed assignments, these could be lambdas. -/
  exprArgs       : Array Expr := #[]
  /-- Map from abstracted level metavariables to parameters. -/
  lmap           : Std.HashMap LMVarId Level := {}
  /-- Map from abstracted expression metavariables to fvars added to `lctx`. -/
  emap           : Std.HashMap MVarId Expr  := {}
  /-- Levels we have visited during abstraction. -/
  levelCache     : Std.HashMap Level Level := {}
  /-- Expressions we have visited during abstraction. -/
  exprCache      : Std.HashMap ExprStructEq Expr := {}
  /-- Level metavariables that are fixed since an fvar in the expression depends on it. -/
  lfixed         : LevelSet := {}
  /-- Expression metavariables that are fixed since an fvar in the expression depends on it. -/
  efixed         : ExprSet := {}

abbrev M := ReaderT Context (StateM State)

@[always_inline]
instance : MonadMCtx M where
  getMCtx := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

def mkFreshId : M Name := do
  modifyGet fun s => (s.ngen.curr, { s with ngen := s.ngen.next })

def mkFreshFVarId : M FVarId :=
  return { name := (← mkFreshId) }

def checkLevelCache (u : Level) (mu' : M Level) : M Level := do
  if let some u' := (← get).levelCache[u]? then
    return u'
  else
    let u' ← mu'
    modify fun s => { s with levelCache := s.levelCache.insert u u' }
    return u'

def checkExprCache (e : Expr) (me' : M Expr) : M Expr := do
  let e : ExprStructEq := ⟨e⟩
  if let some e' := (← get).exprCache[e]? then
    return e'
  else
    let e' ← me'
    modify fun s => { s with exprCache := s.exprCache.insert e e' }
    return e'

partial def abstractLevelMVars (u : Level) : M Level := do
  if (← read).abstractLevels then
    visit (← instantiateLevelMVars u)
  else
    return u
where
  visit (u : Level) : M Level := do
    if !u.hasMVar then
      return u
    else checkLevelCache u do
      match u with
      | Level.zero        => return u
      | Level.param _     => return u
      | Level.succ v      => return u.updateSucc! (← visit v)
      | Level.max v w     => return u.updateMax! (← visit v) (← visit w)
      | Level.imax v w    => return u.updateIMax! (← visit v) (← visit w)
      | Level.mvar mvarId =>
        let s ← get
        let depth := s.mctx.getLevelDepth mvarId
        -- metavariables from lower depths are treated as constants.
        -- fixed metavariables are too (the ones appearing in fvars)
        if depth != s.mctx.depth || s.lfixed.contains u then
          return u
        else if let some u' := s.lmap[mvarId]? then
          return u'
        else
          let paramId := Name.mkNum `_abstMVar s.nextParamIdx
          let u' := Level.param paramId
          modify fun s => {
            s with
            nextParamIdx := s.nextParamIdx + 1
            lmap := s.lmap.insert mvarId u'
            paramNames := s.paramNames.push paramId
            lmvars := s.lmvars.push u }
          return u'

/--
Abstracts metavariables in `e`. Assumes `instantiateMVars` has been applied to `e`.
-/
partial def abstractExprMVars (e : Expr) : M Expr := do
  if !(e.hasExprMVar || ((← read).abstractLevels && e.hasLevelMVar)) then
    return e
  else checkExprCache e do
    match e with
    | e@(Expr.lit _)           => return e
    | e@(Expr.bvar _)          => return e
    | e@(Expr.fvar _)          => return e
    | e@(Expr.sort u)          => return e.updateSort! (← abstractLevelMVars u)
    | e@(Expr.const _ us)      => return e.updateConst! (← us.mapM abstractLevelMVars)
    | e@(Expr.proj _ _ s)      => return e.updateProj! (← abstractExprMVars s)
    | e@(Expr.app f a)         => return e.updateApp! (← abstractExprMVars f) (← abstractExprMVars a)
    | e@(Expr.mdata _ b)       => return e.updateMData! (← abstractExprMVars b)
    | e@(Expr.lam _ d b _)     => return e.updateLambdaE! (← abstractExprMVars d) (← abstractExprMVars b)
    | e@(Expr.forallE _ d b _) => return e.updateForallE! (← abstractExprMVars d) (← abstractExprMVars b)
    | e@(Expr.letE _ t v b _)  => return e.updateLetE! (← abstractExprMVars t) (← abstractExprMVars v) (← abstractExprMVars b)
    | e@(Expr.mvar mvarId)     =>
      let s ← get
      let decl := s.mctx.getDecl mvarId
      -- metavariables from lower depths are treated as constants
      -- fixed metavariables are too (the ones appearing in fvars)
      if decl.depth != s.mctx.depth || s.efixed.contains e then
        return e
      else if let some e' := (← get).emap[mvarId]? then
        return e'
      else
        let type   ← abstractExprMVars (← instantiateMVars decl.type)
        let fvarId ← mkFreshFVarId
        let fvar := Expr.fvar fvarId
        let userName ← if decl.userName.isAnonymous then
          pure <| (`x).appendIndexAfter ((← get).fvars.size + 1)
        else
          pure decl.userName
        let bi := (← read).binderInfo
        modify fun s => {
          s with
          emap  := s.emap.insert mvarId fvar
          fvars := s.fvars.push fvar
          exprArgs := s.exprArgs.push e
          lctx  := s.lctx.mkLocalDecl fvarId userName type bi }
        return fvar

/-- Marks all metavariables appearing in fvars reachable from `e` as fixed. -/
partial def markLCtxMVars (e : Expr) (levelsNotFixed : Bool) : M Unit := do
  let fvars ← collectFVarDeps e
  fvars.forM fun fvar => do
    let (mvars, lmvars) ← collectMVarDeps fvar (lctx := (← get).lctx) (collectLMVars := !levelsNotFixed)
    modify fun s =>
      { s with
        lfixed := if levelsNotFixed then s.lfixed else s.lfixed.insertMany lmvars
        efixed := s.efixed.insertMany mvars }

/--
Runs the `M` monad.

All changes to made to the metavariable context are rolled back.
-/
def runM {α} (mx : M α) (abstractLevels : Bool) (binderInfo : BinderInfo) : MetaM (α × State) := do
  let (x, s) := mx
    |>.run { abstractLevels, binderInfo }
    |>.run { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  return (x, s)

end AbstractMVars

public section

/--
Abstracts metavariables occurring in `e`, creating a lambda expression.
Only metavariables at the current metavariable context depth are abstracted.

Furthermore, for type correctness, the only metavariables that are abstracted are those
that aren't depended upon by the free variables that `e` depends on.
One can compare `abstractMVars` to generalization in the Hindley-Milner type system.

Options:
- If `levels := false`, then level metavariables are not abstracted.
- If `isLambda := false`, then rather than abstract with lambdas, abstracts with foralls.
- If `inferNames := true`, then infers names for anonymous metavariables, like in `mkForallFVars'`.
- `binderInfo` sets the binder info to use for the abstracted metavariables.
- If `levelsNotFixed := true`, then level metavariables are abstracted even if they appear in the local context.
  This is *not correct* to enable, however instance synthesis uses this. It instantiates the level parameters
  with fresh level metavariables and solves for them itself by typechecking.

The result contains
- `lmvars`: An array of the universe level metavariables that were abstracted from `e`.
- `paramNames`: An array of universe level parameters that replaced the corresponding metavariables in `lmvars`.
- `expr`: An expression of the form `fun (x_1 : A_1) ... (x_k : A_k) => e'`, where `k` equals the
  number of expression metavariables abstracted, and `e'` is `e` after we replace the metavariables.
- `exprArgs`: An array of the arguments to apply to `expr` to get an equivalent expression.

The the expression `(expr.instantiateLevelParams paramNames.toList lmvars.toList).beta mvars` is
equivalent to `e`.

Example: Given `f.{?u} ?m2 ?m1`, where `?m1 : ?m2 Nat` and `?m2 : Type -> Type ?u`, this function returns
```
{ lmvars     := #[?u],
  paramNames := #[u],
  mvars      := #[?m2, ?m1],
  expr       := (fun (x_1 : Type -> Type u) (x_2 : x_1 Nat) => f.{u} x_1 x_2) }
```
The actual level parameter name `u` will be different.

## Applications

- This API can be used to "transport" an expression to a different metavariable context.
  Given a new metavariable context, we replace the `AbstractMVarsResult.levels` with
  new fresh universe metavariables, and instantiate the `(m_i : A_i)` in the lambda-expression
  with new fresh metavariables. See `openAbstractMVarsResult`.

- We use this method to cache the results of type class resolution.

- The tactic `MVarId.abstractMVars`.

## Limitations

Currently this procedure does not correctly process delayed assignments.
-/
public def abstractMVars (e : Expr)
    (levels : Bool := true) (isLambda : Bool := true) (inferNames : Bool := false) (binderInfo : BinderInfo := .default)
    (levelsNotFixed : Bool := false) :
    MetaM AbstractMVarsResult := do
  let e ← instantiateMVars e
  let toReset ← if inferNames then setMVarUserNamesAt e (fun _ => true) else pure #[]
  let (e, s) ← AbstractMVars.runM (abstractLevels := levels) (binderInfo := binderInfo) do
    AbstractMVars.markLCtxMVars e (levelsNotFixed := levelsNotFixed)
    AbstractMVars.abstractExprMVars e
  resetMVarUserNames toReset
  let e := if isLambda then s.lctx.mkLambda s.fvars e else s.lctx.mkForall s.fvars e
  return { s with expr := e }

/--
Instantiates an expression abstracted using `abstractMVars`.

Requires that it was abstracted with `isLambda := true`.
-/
def openAbstractMVarsResult (a : AbstractMVarsResult) : MetaM (Array Expr × Array BinderInfo × Expr) := do
  let us ← a.paramNames.mapM fun _ => mkFreshLevelMVar
  let e := a.expr.instantiateLevelParamsArray a.paramNames us
  lambdaMetaTelescope e (some a.numMVars)

/-- Resulting type for `abstractMVarsWithType`. -/
structure AbstractMVarsResultWithType extends AbstractMVarsResult where
  type : Expr

/--
Abstracts metavariables occurring in `ty` or `e`, simultaneously creating both a forall expression and a lambda expression.
Assumes `e : ty`.
See `abstractMVars` for more details.

Returns a result similar to `abstractMVars`, but with an additional `type` field for the abstracted type.
-/
def abstractMVarsWithType (ty : Expr) (e : Expr)
    (levels := true) (inferNames : Bool := false) (binderInfo : BinderInfo := .default) :
    MetaM AbstractMVarsResultWithType := do
  let ty ← instantiateMVars ty
  let e  ← instantiateMVars e
  let toReset ← if inferNames then setMVarUserNamesAt e (fun _ => true) else pure #[]
  let ((ty, e), s) ← AbstractMVars.runM (abstractLevels := levels) (binderInfo := binderInfo)  do
    AbstractMVars.markLCtxMVars ty (levelsNotFixed := false)
    AbstractMVars.markLCtxMVars e (levelsNotFixed := false)
    let ty ← AbstractMVars.abstractExprMVars ty
    let e ← AbstractMVars.abstractExprMVars e
    return (ty, e)
  resetMVarUserNames toReset
  let ty := s.lctx.mkForall s.fvars ty
  let e  := s.lctx.mkLambda s.fvars e
  return { s with type := ty, expr := e }

end

end Lean.Meta
