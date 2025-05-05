/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Util

namespace Lean.Meta

@[inline] private partial def introNImp {σ} (mvarId : MVarId) (n : Nat) (mkName : LocalContext → Name → Bool → σ → MetaM (Name × σ)) (s : σ)
    : MetaM (Array FVarId × MVarId) := mvarId.withContext do
  mvarId.checkNotAssigned `introN
  let mvarType ← mvarId.getType
  let lctx ← getLCtx
  let rec @[specialize] loop (i : Nat) (lctx : LocalContext) (fvars : Array Expr) (j : Nat) (s : σ) (type : Expr) : MetaM (Array Expr × MVarId) := do
    match i, type with
    | 0, type =>
      let type := type.instantiateRevRange j fvars.size fvars
      withLCtx' lctx do
        withNewLocalInstances fvars j do
          let tag     ← mvarId.getTag
          let type := type.headBeta
          let newMVar ← mkFreshExprSyntheticOpaqueMVar type tag
          let newVal  ← mkLambdaFVars fvars newMVar
          mvarId.assign newVal
          return (fvars, newMVar.mvarId!)
    | i+1, .letE n type val body _ =>
      let type   := type.instantiateRevRange j fvars.size fvars
      let type   := type.headBeta
      let val    := val.instantiateRevRange j fvars.size fvars
      let fvarId ← mkFreshFVarId
      let (n, s) ← mkName lctx n true s
      let lctx   := lctx.mkLetDecl fvarId n type val
      let fvar   := mkFVar fvarId
      let fvars  := fvars.push fvar
      loop i lctx fvars j s body
    | i+1, .forallE n type body c =>
      let type   := type.instantiateRevRange j fvars.size fvars
      let type   := type.headBeta
      let fvarId ← mkFreshFVarId
      let (n, s) ← mkName lctx n c.isExplicit s
      let lctx   := lctx.mkLocalDecl fvarId n type c
      let fvar   := mkFVar fvarId
      let fvars  := fvars.push fvar
      loop i lctx fvars j s body
    | i+1, type =>
      if let some (n, type, val, body) := type.letFun? then
        let type   := type.instantiateRevRange j fvars.size fvars
        let type   := type.headBeta
        let val    := val.instantiateRevRange j fvars.size fvars
        let fvarId ← mkFreshFVarId
        let (n, s) ← mkName lctx n true s
        let lctx   := lctx.mkLetDecl fvarId n type val
        let fvar   := mkFVar fvarId
        let fvars  := fvars.push fvar
        loop i lctx fvars j s body
      else
        let type := type.instantiateRevRange j fvars.size fvars
        withLCtx' lctx do
          withNewLocalInstances fvars j do
            /- We used to use just `whnf`, but it produces counterintuitive behavior if
              - `type` is a metavariable `?m` such that `?m := let x := v; b`, or
              - `type` has `MData` or annotations such as `optParam` around a `let`-expression.

              `whnf` instantiates metavariables, and consumes `MData`, but it also expands the `let`.
            -/
            let newType := (← instantiateMVars type).cleanupAnnotations
            if newType.isForall || newType.isLet || newType.isLetFun then
              loop (i+1) lctx fvars fvars.size s newType
            else
              let newType ← whnf newType
              if newType.isForall then
                loop (i+1) lctx fvars fvars.size s newType
              else
                throwTacticEx `introN mvarId "insufficient number of binders"
  let (fvars, mvarId) ← loop n lctx #[] 0 s mvarType
  return (fvars.map Expr.fvarId!, mvarId)

register_builtin_option tactic.hygienic : Bool := {
  defValue := true
  group    := "tactic"
  descr    := "make sure tactics are hygienic"
}

private def mkFreshBinderNameForTacticCore (lctx : LocalContext) (binderName : Name) (hygienic := true) : MetaM Name := do
  if hygienic then
    mkFreshUserName binderName
  else
    return lctx.getUnusedName binderName

/--
Similar to `Lean.Core.mkFreshUserName`, but takes into account the `tactic.hygienic` option value.
If `tactic.hygienic = true`, then fresh macro scopes are applied to `binderName`.
If not, then returns an (accessible) name based on `binderName` that is unused in the local context.
-/
def mkFreshBinderNameForTactic (binderName : Name) : MetaM Name := do
  mkFreshBinderNameForTacticCore (← getLCtx) binderName (tactic.hygienic.get (← getOptions))

private def mkAuxNameImp (preserveBinderNames : Bool) (hygienic : Bool) (useNamesForExplicitOnly : Bool)
    (lctx : LocalContext) (binderName : Name) (isExplicit : Bool) : List Name → MetaM (Name × List Name)
  | []         => mkAuxNameWithoutGivenName []
  | n :: rest  => do
    if useNamesForExplicitOnly && !isExplicit then
      mkAuxNameWithoutGivenName (n :: rest)
    else if n != Name.mkSimple "_" then
      return (n, rest)
    else
      mkAuxNameWithoutGivenName rest
where
  mkAuxNameWithoutGivenName (rest : List Name) : MetaM (Name × List Name) := do
    -- Use a nicer binder name than `[anonymous]`, which can appear in for example `letFun x f` when `f` is not a lambda expression.
    -- In this case, we make sure the name is hygienic.
    let binderName ← if binderName.isAnonymous then mkFreshUserName `a else pure binderName
    if preserveBinderNames then
      return (binderName, rest)
    else
      let binderName ← mkFreshBinderNameForTacticCore lctx binderName hygienic
      return (binderName, rest)

def introNCore (mvarId : MVarId) (n : Nat) (givenNames : List Name) (useNamesForExplicitOnly : Bool) (preserveBinderNames : Bool)
    : MetaM (Array FVarId × MVarId) := do
  let hygienic := tactic.hygienic.get (← getOptions)
  if n == 0 then
    return (#[], mvarId)
  else
    introNImp mvarId n (mkAuxNameImp preserveBinderNames hygienic useNamesForExplicitOnly) givenNames

/--
Introduce `n` binders in the goal `mvarId`.
-/
abbrev _root_.Lean.MVarId.introN (mvarId : MVarId) (n : Nat) (givenNames : List Name := []) (useNamesForExplicitOnly := false) : MetaM (Array FVarId × MVarId) :=
  introNCore mvarId n givenNames (useNamesForExplicitOnly := useNamesForExplicitOnly) (preserveBinderNames := false)

/--
Introduce `n` binders in the goal `mvarId`. The new hypotheses are named using the binder names.
The suffix `P` stands for "preserving`.
-/
abbrev _root_.Lean.MVarId.introNP (mvarId : MVarId) (n : Nat) : MetaM (Array FVarId × MVarId) :=
  introNCore mvarId n [] (useNamesForExplicitOnly := false) (preserveBinderNames := true)

/--
Introduce one binder using `name` as the new hypothesis name.
-/
def _root_.Lean.MVarId.intro (mvarId : MVarId) (name : Name) : MetaM (FVarId × MVarId) := do
  let (fvarIds, mvarId) ← mvarId.introN 1 [name]
  return (fvarIds[0]!, mvarId)

def intro1Core (mvarId : MVarId) (preserveBinderNames : Bool) : MetaM (FVarId × MVarId) := do
  let (fvarIds, mvarId) ← introNCore mvarId 1 [] (useNamesForExplicitOnly := false) preserveBinderNames
  return (fvarIds[0]!, mvarId)

/-- Introduce one object from the goal `mvarid`, without preserving the name used in the binder.
Returns a pair made of the newly introduced variable (which will have an inaccessible name)
and the new goal. This will fail if there is nothing to introduce, ie when the goal
does not start with a forall, lambda or let. -/
abbrev _root_.Lean.MVarId.intro1 (mvarId : MVarId) : MetaM (FVarId × MVarId) :=
  intro1Core mvarId false

/-- Introduce one object from the goal `mvarid`, preserving the name used in the binder.
Returns a pair made of the newly introduced variable and the new goal.
This will fail if there is nothing to introduce, ie when the goal
does not start with a forall, lambda or let. -/
abbrev _root_.Lean.MVarId.intro1P (mvarId : MVarId) : MetaM (FVarId × MVarId) :=
  intro1Core mvarId true

/--
Calculate the number of new hypotheses that would be created by `intros`,
i.e. the number of binders which can be introduced without unfolding definitions.
-/
partial def getIntrosSize : Expr → Nat
  | .forallE _ _ b _ => getIntrosSize b + 1
  | .letE _ _ _ b _  => getIntrosSize b + 1
  | .mdata _ b       => getIntrosSize b
  | e                =>
    if let some (_, _, _, b) := e.letFun? then
      getIntrosSize b + 1
    else
      0

/--
Introduce as many binders as possible without unfolding definitions.
-/
def _root_.Lean.MVarId.intros (mvarId : MVarId) : MetaM (Array FVarId × MVarId) := do
  let type ← mvarId.getType
  let type ← instantiateMVars type
  let n := getIntrosSize type
  if n == 0 then
    return (#[], mvarId)
  else
    mvarId.introN n

end Lean.Meta
