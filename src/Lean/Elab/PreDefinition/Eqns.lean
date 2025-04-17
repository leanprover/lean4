/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Eqns
import Lean.Meta.CtorRecognizer
import Lean.Util.CollectFVars
import Lean.Util.ForEachExprWhere
import Lean.Meta.Tactic.Split
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Refl
import Lean.Meta.Match.MatchEqs

namespace Lean.Elab.Eqns
open Meta

structure EqnInfoCore where
  declName    : Name
  levelParams : List Name
  type        : Expr
  value       : Expr
  deriving Inhabited

/--
Zeta reduces `let` and `let_fun` while consuming metadata.
Returns true if progress is made.
-/
partial def expand (progress : Bool) (e : Expr) : Bool × Expr :=
  match e with
  | Expr.letE _ _ v b _ => expand true (b.instantiate1 v)
  | Expr.mdata _ b      => expand true b
  | e =>
    if let some (_, _, v, b) := e.letFun? then
      expand true (b.instantiate1 v)
    else
      (progress, e)

def expandRHS? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | return none
  let (true, rhs') := expand false rhs | return none
  return some (← mvarId.replaceTargetDefEq (← mkEq lhs rhs'))

def simpMatch? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let mvarId' ← Split.simpMatchTarget mvarId
  if mvarId != mvarId' then return some mvarId' else return none

def simpIf? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let mvarId' ← simpIfTarget mvarId (useDecide := true)
  if mvarId != mvarId' then return some mvarId' else return none

private def findMatchToSplit? (deepRecursiveSplit : Bool) (env : Environment) (e : Expr)
    (declNames : Array Name) (exceptionSet : ExprSet) : Option Expr :=
  e.findExt? fun e => Id.run do
    if e.hasLooseBVars || exceptionSet.contains e then
      return Expr.FindStep.visit
    else if let some info := isMatcherAppCore? env e then
      let args := e.getAppArgs
      -- If none of the discriminants is a free variable, then it is not worth splitting the match
      let mut hasFVarDiscr := false
      for i in [info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs] do
        let discr := args[i]!
        if discr.isFVar then
          hasFVarDiscr := true
          break
      unless hasFVarDiscr do
        return Expr.FindStep.visit
      -- For non-recursive functions (`declNames` empty), we split here
      if declNames.isEmpty then
          return Expr.FindStep.found
      -- For recursive functions, the “new” behavior is to likewise split
      if deepRecursiveSplit then
          return Expr.FindStep.found
      -- Else, the “old” behavior is split only when at least one alternative contains a `declNames`
      -- application with loose bound variables.
      for i in [info.getFirstAltPos : info.getFirstAltPos + info.numAlts] do
        let alt := args[i]!
        if Option.isSome <| alt.find? fun e => declNames.any e.isAppOf && e.hasLooseBVars then
          return Expr.FindStep.found
      return Expr.FindStep.visit
    else
      let Expr.const declName .. := e.getAppFn | return Expr.FindStep.visit
      if declName == ``WellFounded.fix || isBRecOnRecursor env declName then
        -- We should not go inside unfolded nested recursive applications
        return Expr.FindStep.done
      else
        return Expr.FindStep.visit

partial def splitMatch? (mvarId : MVarId) (declNames : Array Name) : MetaM (Option (List MVarId)) := commitWhenSome? do
  let target ← mvarId.getType'
  let rec go (badCases : ExprSet) : MetaM (Option (List MVarId)) := do
    if let some e := findMatchToSplit? (backward.eqns.deepRecursiveSplit.get (← getOptions)) (← getEnv)
                                       target declNames badCases then
      try
        Meta.Split.splitMatch mvarId e
      catch _ =>
        go (badCases.insert e)
    else
      trace[Meta.Tactic.split] "did not find term to split\n{MessageData.ofGoal mvarId}"
      return none
  go {}

private def lhsDependsOn (type : Expr) (fvarId : FVarId) : MetaM Bool :=
  forallTelescope type fun _ type => do
    if let some (_, lhs, _) ← matchEq? type then
      dependsOn lhs fvarId
    else
      dependsOn type fvarId

/-- Try to close goal using `rfl` with smart unfolding turned off. -/
def tryURefl (mvarId : MVarId) : MetaM Bool :=
  withOptions (smartUnfolding.set · false) do
    try mvarId.refl; return true catch _ => return false

/--
  Eliminate `namedPatterns` from equation, and trivial hypotheses.
-/
def simpEqnType (eqnType : Expr) : MetaM Expr := do
  forallTelescopeReducing (← instantiateMVars eqnType) fun ys type => do
    let proofVars := collect type
    trace[Elab.definition] "simpEqnType type: {type}"
    let mut type ← Match.unfoldNamedPattern type
    let mut eliminated : FVarIdSet := {}
    for y in ys.reverse do
      trace[Elab.definition] ">> simpEqnType: {← inferType y}, {type}"
      if proofVars.contains y.fvarId! then
        let some (_, Expr.fvar fvarId, rhs) ← matchEq? (← inferType y) | throwError "unexpected hypothesis in alternative{indentExpr eqnType}"
        eliminated := eliminated.insert fvarId
        type := type.replaceFVarId fvarId rhs
      else if eliminated.contains y.fvarId! then
        if (← dependsOn type y.fvarId!) then
          type ← mkForallFVars #[y] type
      else
        if let some (_, lhs, rhs) ← matchEq? (← inferType y) then
          if (← isDefEq lhs rhs) then
            if !(← dependsOn type y.fvarId!) then
              continue
            else if !(← lhsDependsOn type y.fvarId!) then
              -- Since the `lhs` of the `type` does not depend on `y`, we replace it with `Eq.refl` in the `rhs`
              type := type.replaceFVar y (← mkEqRefl lhs)
              continue
        type ← mkForallFVars #[y] type
    return type
where
  -- Collect eq proof vars used in `namedPatterns`
  collect (e : Expr) : FVarIdSet :=
    let go (e : Expr) (ω) : ST ω FVarIdSet := do
      let ref ← ST.mkRef {}
      e.forEachWhere Match.isNamedPattern fun e => do
        let some e := Match.isNamedPattern? e | unreachable!
        let arg := e.appArg!.consumeMData
        if arg.isFVar then
          ST.Prim.Ref.modify ref (·.insert arg.fvarId!)
      ST.Prim.Ref.get ref
    runST (go e)

private partial def saveEqn (mvarId : MVarId) : StateRefT (Array Expr) MetaM Unit := mvarId.withContext do
  let target ← mvarId.getType'
  let fvarState := collectFVars {} target
  let fvarState ← (← getLCtx).foldrM (init := fvarState) fun decl fvarState => do
    if fvarState.fvarSet.contains decl.fvarId then
      return collectFVars fvarState (← instantiateMVars decl.type)
    else
      return fvarState
  let mut fvarIdSet := fvarState.fvarSet
  let mut fvarIds ← sortFVarIds <| fvarState.fvarSet.toArray
  -- Include (relevant) propositions that are not already in `fvarIdSet`
  let mut modified := false
  repeat
    modified := false
    for decl in (← getLCtx) do
      unless fvarIdSet.contains decl.fvarId do
        if (← isProp decl.type) then
          let type ← instantiateMVars decl.type
          unless (← isIrrelevant fvarIdSet type) do
            modified := true
            (fvarIdSet, fvarIds) ← pushDecl fvarIdSet fvarIds decl
  until !modified
  let type ← mkForallFVars (fvarIds.map mkFVar) target
  let type ← simpEqnType type
  modify (·.push type)
where
  /--
    We say the type/proposition is "irrelevant" if
    1- It does not contain any variable in `fvarIdSet` OR
    2- It is of the form `x = t` or `t = x` where `x` is a free variable
       that is not in `fvarIdSet`. This can of equality can be eliminated by substitution.  -/
  isIrrelevant (fvarIdSet : FVarIdSet) (type : Expr) : MetaM Bool := do
    if Option.isNone <| type.find? fun e => e.isFVar && fvarIdSet.contains e.fvarId! then
      return true
    else if let some (_, lhs, rhs) := type.eq? then
      return (lhs.isFVar && !fvarIdSet.contains lhs.fvarId!)
             || (rhs.isFVar && !fvarIdSet.contains rhs.fvarId!)
    else
      return false

  pushDecl (fvarIdSet : FVarIdSet) (fvarIds : Array FVarId) (localDecl : LocalDecl) : MetaM (FVarIdSet × Array FVarId) := do
    let (fvarIdSet, fvarIds) ← collectDeps fvarIdSet fvarIds (← instantiateMVars localDecl.type)
    return (fvarIdSet.insert localDecl.fvarId, fvarIds.push localDecl.fvarId)

  collectDeps (fvarIdSet : FVarIdSet) (fvarIds : Array FVarId) (type : Expr) : MetaM (FVarIdSet × Array FVarId) := do
    let s := collectFVars {} type
    let usedFVarIds ← sortFVarIds <| s.fvarSet.toArray
    let mut fvarIdSet := fvarIdSet
    let mut fvarIds := fvarIds
    for fvarId in usedFVarIds do
      unless fvarIdSet.contains fvarId do
        (fvarIdSet, fvarIds) ← pushDecl fvarIdSet fvarIds (← fvarId.getDecl)
    return (fvarIdSet, fvarIds)

/--
  Quick filter for deciding whether to use `simpMatch?` at `mkEqnTypes`.
  If the result is `false`, then it is not worth trying `simpMatch`.
-/
private def shouldUseSimpMatch (e : Expr) : MetaM Bool := do
  let env ← getEnv
  let find (root : Expr) : ExceptT Unit MetaM Unit :=
    root.forEach fun e => do
      if let some info := isMatcherAppCore? env e then
        let args := e.getAppArgs
        for discr in args[info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs] do
          if (← Meta.isConstructorApp discr) then
            throwThe Unit ()
  return (← (find e).run) matches .error _

partial def mkEqnTypes (declNames : Array Name) (mvarId : MVarId) : MetaM (Array Expr) := do
  let (_, eqnTypes) ← go mvarId |>.run #[]
  return eqnTypes
where
  go (mvarId : MVarId) : StateRefT (Array Expr) MetaM Unit := do
    trace[Elab.definition.eqns] "mkEqnTypes step\n{MessageData.ofGoal mvarId}"

    if let some mvarId ← expandRHS? mvarId then
      return (← go mvarId)

    if (← shouldUseSimpMatch (← mvarId.getType')) then
      if let some mvarId ← simpMatch? mvarId then
        return (← go mvarId)

    if let some mvarIds ← splitMatch? mvarId declNames then
      return (← mvarIds.forM go)

    saveEqn mvarId

/--
  Some of the hypotheses added by `mkEqnTypes` may not be used by the actual proof (i.e., `value` argument).
  This method eliminates them.

  Alternative solution: improve `saveEqn` and make sure it never includes unnecessary hypotheses.
  These hypotheses are leftovers from tactics such as `splitMatch?` used in `mkEqnTypes`.
-/
def removeUnusedEqnHypotheses (declType declValue : Expr) : CoreM (Expr × Expr) := do
  go declType declValue #[] {}
where
  go (type value : Expr) (xs : Array Expr) (lctx : LocalContext) : CoreM (Expr × Expr) := do
    match value with
    | .lam n d b bi =>
      let d := d.instantiateRev xs
      let fvarId ← mkFreshFVarId
      go (type.bindingBody!) b (xs.push (mkFVar fvarId)) (lctx.mkLocalDecl fvarId n d bi)
    | _ =>
      let type  := type.instantiateRev xs
      let value := value.instantiateRev xs
      let mut s := collectFVars (collectFVars {} type) value
      let mut xsNew := #[]
      for x in xs.reverse do
        if s.fvarSet.contains x.fvarId! then
          s := collectFVars s (lctx.getFVar! x).type
          xsNew := xsNew.push x
      if xsNew.size == xs.size then
        return (declType, declValue)
      else
        xsNew := xsNew.reverse
        return (lctx.mkForall xsNew type, lctx.mkLambda xsNew value)

/-- Delta reduce the equation left-hand-side -/
def deltaLHS (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | throwTacticEx `deltaLHS mvarId "equality expected"
  let some lhs ← delta? lhs | throwTacticEx `deltaLHS mvarId "failed to delta reduce lhs"
  mvarId.replaceTargetDefEq (← mkEq lhs rhs)

def deltaRHS? (mvarId : MVarId) (declName : Name) : MetaM (Option MVarId) := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | return none
  let some rhs ← delta? rhs.consumeMData (· == declName) | return none
  mvarId.replaceTargetDefEq (← mkEq lhs rhs)

private partial def whnfAux (e : Expr) : MetaM Expr := do
  let e ← whnfI e -- Must reduce instances too, otherwise it will not be able to reduce `(Nat.rec ... ... (OfNat.ofNat 0))`
  let f := e.getAppFn
  match f with
  | .proj _ _ s => return mkAppN (f.updateProj! (← whnfAux s)) e.getAppArgs
  | _ => return e

/-- Apply `whnfR` to lhs, return `none` if `lhs` was not modified -/
def whnfReducibleLHS? (mvarId : MVarId) : MetaM (Option MVarId) := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | return none
  let lhs' ← whnfAux lhs
  if lhs' != lhs then
    return some (← mvarId.replaceTargetDefEq (← mkEq lhs' rhs))
  else
    return none

def tryContradiction (mvarId : MVarId) : MetaM Bool := do
  mvarId.contradictionCore { genDiseq := true }

/--
Returns the type of the unfold theorem, as the starting point for calculating the equational
types.
-/
private def unfoldThmType (declName : Name) : MetaM Expr := do
  if let some unfoldThm ← getUnfoldEqnFor? declName (nonRec := false) then
    let info ← getConstInfo unfoldThm
    pure info.type
  else
    let info ← getConstInfoDefn declName
    let us := info.levelParams.map mkLevelParam
    lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
      let type ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
      mkForallFVars xs type

private def unfoldLHS (declName : Name) (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  if let some unfoldThm ← getUnfoldEqnFor? declName (nonRec := false) then
    -- Recursive definition: Use unfolding lemma
    let mut mvarId := mvarId
    let target ← mvarId.getType'
    let some (_, lhs, rhs) := target.eq? | throwError "unfoldLHS: Unexpected target {target}"
    unless lhs.isAppOf declName do throwError "unfoldLHS: Unexpected LHS {lhs}"
    let h := mkAppN (.const unfoldThm lhs.getAppFn.constLevels!) lhs.getAppArgs
    let some (_, _, lhsNew) := (← inferType h).eq? | unreachable!
    let targetNew ← mkEq lhsNew rhs
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
    mvarId.assign (← mkEqTrans h mvarNew)
    return mvarNew.mvarId!
  else
    -- Else use delta reduction
    deltaLHS mvarId

private partial def mkEqnProof (declName : Name) (type : Expr) (tryRefl : Bool) : MetaM Expr := do
  trace[Elab.definition.eqns] "proving: {type}"
  withNewMCtxDepth do
    let main ← mkFreshExprSyntheticOpaqueMVar type
    let (_, mvarId) ← main.mvarId!.intros

    -- Try rfl before deltaLHS to avoid `id` checkpoints in the proof, which would make
    -- the lemma ineligible for dsimp
    -- For well-founded recursion this is disabled: The equation may hold
    -- definitionally as written, but not embedded in larger proofs
    if tryRefl then
      if (← withAtLeastTransparency .all (tryURefl mvarId)) then
        return ← instantiateMVars main

    go (← unfoldLHS declName mvarId)
    instantiateMVars main
  where
  /--
  The core loop of proving an equation. Assumes that the function call on the left-hand side has
  already been unfolded, using whatever method applies to the current function definition strategy.

  Currently used for non-recursive functions and partial fixpoints; maybe later well-founded
  recursion and structural recursion can and should use this too.
  -/
  go (mvarId : MVarId) : MetaM Unit := do
    trace[Elab.definition.eqns] "step\n{MessageData.ofGoal mvarId}"
    if ← withAtLeastTransparency .all (tryURefl mvarId) then
      return ()
    else if (← tryContradiction mvarId) then
      return ()
    else if let some mvarId ← simpMatch? mvarId then
      go mvarId
    else if let some mvarId ← simpIf? mvarId then
      go mvarId
    else if let some mvarId ← whnfReducibleLHS? mvarId then
      go mvarId
    else
      let ctx ← Simp.mkContext (config := { dsimp := false })
      match (← simpTargetStar mvarId ctx (simprocs := {})).1 with
      | TacticResultCNM.closed => return ()
      | TacticResultCNM.modified mvarId => go mvarId
      | TacticResultCNM.noChange =>
        if let some mvarIds ← casesOnStuckLHS? mvarId then
          mvarIds.forM go
        else if let some mvarIds ← splitTarget? mvarId then
          mvarIds.forM go
        else
          throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId}"


/--
Generate equations for `declName`.

This unfolds the function application on the LHS (using an unfold theorem, if present, or else by
delta-reduction), calculates the types for the equational theorems using `mkEqnTypes`, and then
proves them using `mkEqnProof`.

This is currently used for non-recursive functions, well-founded recursion and partial_fixpoint,
but not for structural recursion.
-/
def mkEqns (declName : Name) (declNames : Array Name) (tryRefl := true): MetaM (Array Name) := do
  let info ← getConstInfoDefn declName
  let us := info.levelParams.map mkLevelParam
  withOptions (tactic.hygienic.set · false) do
  let target ← unfoldThmType declName
  let eqnTypes ← withNewMCtxDepth <|
    forallTelescope (cleanupAnnotations := true) target fun xs target => do
      let goal ← mkFreshExprSyntheticOpaqueMVar target
      withReducible do
        mkEqnTypes declNames goal.mvarId!
  let mut thmNames := #[]
  for h : i in [: eqnTypes.size] do
    let type := eqnTypes[i]
    trace[Elab.definition.eqns] "eqnType[{i}]: {eqnTypes[i]}"
    let name := (Name.str declName eqnThmSuffixBase).appendIndexAfter (i+1)
    thmNames := thmNames.push name
    -- determinism: `type` should be independent of the environment changes since `baseName` was
    -- added
    realizeConst declName name (doRealize name info type)
  return thmNames
where
  doRealize name info type := withOptions (tactic.hygienic.set · false) do
    let value ← mkEqnProof declName type tryRefl
    let (type, value) ← removeUnusedEqnHypotheses type value
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }

/--
  Auxiliary method for `mkUnfoldEq`. The structure is based on `mkEqnTypes`.
  `mvarId` is the goal to be proved. It is a goal of the form
  ```
  declName x_1 ... x_n = body[x_1, ..., x_n]
  ```
  The proof is constructed using the automatically generated equational theorems.
  We basically keep splitting the `match` and `if-then-else` expressions in the right hand side
  until one of the equational theorems is applicable.
-/
partial def mkUnfoldProof (declName : Name) (mvarId : MVarId) : MetaM Unit := do
  let some eqs ← getEqnsFor? declName | throwError "failed to generate equations for '{declName}'"
  let tryEqns (mvarId : MVarId) : MetaM Bool :=
    eqs.anyM fun eq => commitWhen do checkpointDefEq (mayPostpone := false) do
      try
        let subgoals ← mvarId.apply (← mkConstWithFreshMVarLevels eq)
        subgoals.allM fun subgoal => do
          if (← subgoal.isAssigned) then
            return true -- Subgoal was already solved. This can happen when there are dependencies between the subgoals
          else
            subgoal.assumptionCore
      catch _ =>
        return false
  let rec go (mvarId : MVarId) : MetaM Unit := do
    if (← tryEqns mvarId) then
      return ()

    if (← shouldUseSimpMatch (← mvarId.getType')) then
      if let some mvarId ← simpMatch? mvarId then
        return (← go mvarId)

    if let some mvarIds ← splitTarget? mvarId (splitIte := false) then
      return (← mvarIds.forM go)

    if (← tryContradiction mvarId) then
      return ()

    throwError "failed to generate unfold theorem for '{declName}'\n{MessageData.ofGoal mvarId}"
  go mvarId

/-- Generate the "unfold" lemma for `declName`. -/
def mkUnfoldEq (declName : Name) (info : EqnInfoCore) : MetaM Name := do
  let name := Name.str declName unfoldThmSuffix
  realizeConst declName name (doRealize name)
  return name
where
  doRealize name := withOptions (tactic.hygienic.set · false) do
    lambdaTelescope info.value fun xs body => do
      let us := info.levelParams.map mkLevelParam
      let type ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
      let goal ← mkFreshExprSyntheticOpaqueMVar type
      mkUnfoldProof declName goal.mvarId!
      let type ← mkForallFVars xs type
      let value ← mkLambdaFVars xs (← instantiateMVars goal)
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := info.levelParams
      }

def getUnfoldFor? (declName : Name) (getInfo? : Unit → Option EqnInfoCore) : MetaM (Option Name) := do
  if let some info := getInfo? () then
    return some (← mkUnfoldEq declName info)
  else
    return none

builtin_initialize
  registerTraceClass `Elab.definition.unfoldEqn
  registerTraceClass `Elab.definition.eqns

end Lean.Elab.Eqns
