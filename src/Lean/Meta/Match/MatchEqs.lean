/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.Match
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.SplitIf

namespace Lean.Meta.Match

-- TODO enviroment extension for caching conditional equation lemmas and splitter for match auxiliary declarations.

private def isMatchValue (e : Expr) : Bool :=
  e.isNatLit || e.isCharLit || e.isStringLit

/--
  Helper method. Recall that alternatives that do not have variables have a `Unit` parameter to ensure
  they are not eagerly evaluated. -/
private def toFVarsRHSArgs (ys : Array Expr) (resultType : Expr) : MetaM (Array Expr × Array Expr) := do
  if ys.size == 1 then
    if (← inferType ys[0]).isConstOf ``Unit && !(← dependsOn resultType ys[0].fvarId!) then
      return (#[], #[mkConst ``Unit.unit])
  return (ys, ys)

/--
  Simplify/filter hypotheses that ensure that a match alternative does not match the previous ones.
  Remark: if there is no overlaping between the alternatives, the empty array is returned. -/
private partial def simpHs (hs : Array Expr) (numPatterns : Nat) : MetaM (Array Expr) := do
  hs.filterMapM fun h => forallTelescope h fun ys _ => do
    trace[Meta.debug] "ys: {ys}"
    let xs  := ys[:ys.size - numPatterns].toArray
    let eqs ← ys[ys.size - numPatterns : ys.size].toArray.mapM inferType
    if let some eqsNew ← simpEqs eqs *> get |>.run |>.run' #[] then
      let newH ← eqsNew.foldrM (init := mkConst ``False) mkArrow
      let xs ← xs.filterM fun x => dependsOn newH x.fvarId!
      return some (← mkForallFVars xs newH)
    else
      none
where
  simpEq (lhs : Expr) (rhs : Expr) : OptionT (StateRefT (Array Expr) MetaM) Unit := do
    if isMatchValue lhs && isMatchValue rhs then
      unless (← isDefEq lhs rhs) do
        failure
    else if rhs.isFVar then
      -- Ignore case since it matches anything
      pure ()
    else match lhs.arrayLit?, rhs.arrayLit? with
      | some (_, lhsArgs), some (_, rhsArgs) =>
        if lhsArgs.length != rhsArgs.length then
          failure
        else
          for lhsArg in lhsArgs, rhsArg in rhsArgs do
            simpEq lhsArg rhsArg
      | _, _ =>
        match toCtorIfLit lhs |>.constructorApp? (← getEnv), toCtorIfLit rhs |>.constructorApp? (← getEnv) with
        | some (lhsCtor, lhsArgs), some (rhsCtor, rhsArgs) =>
          if lhsCtor.name == rhsCtor.name then
            for lhsArg in lhsArgs[lhsCtor.numParams:], rhsArg in rhsArgs[lhsCtor.numParams:] do
              simpEq lhsArg rhsArg
          else
            failure
        | _, _ =>
          let newEq ← mkEq lhs rhs
          modify fun eqs => eqs.push newEq

  simpEqs (eqs : Array Expr) : OptionT (StateRefT (Array Expr) MetaM) Unit := do
    eqs.forM fun eq =>
      match eq.eq? with
      | some (_, lhs, rhs) => simpEq lhs rhs
      | _ => throwError "failed to generate equality theorems for 'match', equality expected{indentExpr eq}"


/--
  Helper method for `proveCondEqThm`. Given a goal of the form `C.rec ... xMajor = rhs`,
  apply `cases xMajor`. -/
private def casesOnStuckLHS (mvarId : MVarId) : MetaM (Array MVarId) := do
  let target ← getMVarType mvarId
  if let some (_, lhs, rhs) ← matchEq? target then
    matchConstRec lhs.getAppFn (fun _ => failed) fun recVal _ => do
      let args := lhs.getAppArgs
      if recVal.getMajorIdx >= args.size then failed
      let mut major := args[recVal.getMajorIdx]
      unless major.isFVar do failed
      return (← cases mvarId major.fvarId!).map fun s => s.mvarId
  else
    failed
where
  failed {α} : MetaM α := throwError "'casesOnStuckLHS' failed"

/--
  Helper method for proving a conditional equational theorem associated with an alternative of
  the `match`-eliminator `matchDeclName`. `type` contains the type of the theorem. -/
partial def proveCondEqThm (matchDeclName : Name) (type : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  withLCtx {} {} <| forallTelescope type fun ys target => do
    let mvar0  ← mkFreshExprSyntheticOpaqueMVar target
    let mvarId ← deltaTarget mvar0.mvarId! (. == matchDeclName)
    trace[Meta.Match.matchEqs] "{MessageData.ofGoal mvarId}"
    go mvarId 0
    mkLambdaFVars ys (← instantiateMVars mvar0)
where
  go (mvarId : MVarId) (depth : Nat) : MetaM Unit := withIncRecDepth do
    let mvarId' ← modifyTargetEqLHS mvarId whnfCore
    let mvarId := mvarId'
    trace[Meta.debug] "proveLoop [{depth}]\n{MessageData.ofGoal mvarId}"
    let subgoals ←
      (do applyRefl mvarId; return #[])
      <|>
      (do contradiction mvarId { genDiseq := true }; return #[])
      <|>
      (casesOnStuckLHS mvarId)
      <|>
      (do let mvarId' ← simpIfTarget mvarId (useDecide := true)
          if mvarId' == mvarId then throwError "simpIf failed"
          return #[mvarId'])
      <|>
      (do if let some (s₁, s₂) ← splitIfTarget? mvarId then
            let mvarId₁ ← trySubst s₁.mvarId s₁.fvarId
            return #[mvarId₁, s₂.mvarId]
          else
            throwError "spliIf failed")
      <|>
      (throwError "failed to generate equality theorems for `match` expression, support for array literals has not been implemented yet\n{MessageData.ofGoal mvarId}")
    subgoals.forM (go . (depth+1))


/-- Construct new local declarations `xs` with types `altTypes`, and then execute `f xs`  -/
private partial def withSplitterAlts (altTypes : Array Expr) (f : Array Expr → MetaM α) : MetaM α := do
  let rec go (i : Nat) (xs : Array Expr) : MetaM α := do
    if h : i < altTypes.size then
      let hName := (`h).appendIndexAfter (i+1)
      withLocalDeclD hName (altTypes.get ⟨i, h⟩) fun x =>
        go (i+1) (xs.push x)
    else
      f xs
  go 0 #[]

/--
  Construct a proof for the splitter generated by `mkEquationsfor`.
  The proof uses the definition of the `match`-declaration as a template (argument `template`).
  - `alts` are free variables corresponding to alternatives of the `match` auxiliary declaration being processed.
  - `altNews` are the new free variables which contains aditional hypotheses that ensure they are only used
     when the previous overlapping alternatives are not applicable. -/
private partial def mkSplitterProof (matchDeclName : Name) (template : Expr) (alts altsNew : Array Expr) : MetaM Expr := do
  trace[Meta.Match.matchEqs] "proof template: {template}"
  let map := mkMap
  let (proof, mvarIds) ← convertTemplate map |>.run #[]
  trace[Meta.Match.matchEqs] "splitter proof: {proof}"
  for mvarId in mvarIds do
    trace[Meta.Match.matchEqs] "subgoal {mkMVar mvarId}, {repr (← getMVarDecl mvarId).kind}, {← isExprMVarAssigned mvarId}\n{MessageData.ofGoal mvarId}"
    let (_, mvarId) ← intros mvarId
    let mvarId ← tryClearMany mvarId (alts.map (·.fvarId!))
    unless (← contradictionCore mvarId {}) do
      -- TODO
      trace[Meta.Match.matchEqs] "failed to generate splitter, unsolved subgoal\n{MessageData.ofGoal mvarId}"
      admit mvarId
      -- throwError "failed to generate splitter for match auxiliary declaration '{matchDeclName}', unsolved subgoal:\n{MessageData.ofGoal mvarId}"
  instantiateMVars proof
where
  mkMap : NameMap Expr := do
    let mut m := {}
    for alt in alts, altNew in altsNew do
      m := m.insert alt.fvarId! altNew
    return m

  convertTemplate (m : NameMap Expr) : StateRefT (Array MVarId) MetaM Expr :=
    transform template fun e => do
      match e.getAppFn with
      | Expr.fvar fvarId .. =>
        match m.find? fvarId with
        | some altNew =>
          trace[Meta.Match.matchEqs] ">> {e}, {altNew}"
          let eNew ←
            if (← shouldCopyArgs e) then
              addExtraParams (mkAppN altNew e.getAppArgs)
            else
              addExtraParams altNew
          return TransformStep.done eNew
        | none => return TransformStep.visit e
      | _ => return TransformStep.visit e

  shouldCopyArgs (e : Expr) : MetaM Bool := do
    if e.getAppNumArgs == 1 then
      match (← whnfD (← inferType e.appFn!)) with
      | Expr.forallE _ d b _ =>
        /- If result type does not depend on the argument, then
           argument is an auxiliary unit used because Lean is an eager language, we should not copy it. -/
        return b.hasLooseBVar 0
      | _ => unreachable!
    return true

  addExtraParams (e : Expr) : StateRefT (Array MVarId) MetaM Expr := do
    trace[Meta.Match.matchEqs] "addExtraParams {e}"
    let (mvars, _, _) ← forallMetaTelescopeReducing (← inferType e) (kind := MetavarKind.syntheticOpaque)
    modify fun s => s ++ (mvars.map (·.mvarId!))
    return mkAppN e mvars

/--
  Create conditional equations and splitter for the given match auxiliary declaration. -/
partial def mkEquationsFor (matchDeclName : Name) :  MetaM Unit := do
  -- TODO: do not assume `mkEquationsFor` was not already generated
  let constInfo ← getConstInfo matchDeclName
  let us := constInfo.levelParams.map mkLevelParam
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "'{matchDeclName}' is not a matcher function"
  forallTelescopeReducing constInfo.type fun xs matchResultType => do
    let params := xs[:matchInfo.numParams]
    let motive := xs[matchInfo.getMotivePos]
    let alts   := xs[xs.size - matchInfo.numAlts:]
    let firstDiscrIdx := matchInfo.numParams + 1
    let discrs := xs[firstDiscrIdx : firstDiscrIdx + matchInfo.numDiscrs]
    let mut notAlts := #[]
    let mut idx := 1
    let mut splitterAltTypes := #[]
    for alt in alts do
      let altType ← inferType alt
      trace[Meta.debug] ">> {altType}"
      let (notAlt, splitterAltType) ← forallTelescopeReducing altType fun ys altResultType => do
        let (ys, rhsArgs) ← toFVarsRHSArgs ys altResultType
        let patterns := altResultType.getAppArgs
        let mut hs := #[]
        for notAlt in notAlts do
          hs := hs.push (← instantiateForall notAlt patterns)
        hs ← simpHs hs patterns.size
        trace[Meta.Match.matchEqs] "hs: {hs}"
        let splitterAltType ← mkForallFVars ys (← hs.foldrM (init := altResultType) mkArrow)
        -- Create a proposition for representing terms that do not match `patterns`
        let mut notAlt := mkConst ``False
        for discr in discrs.toArray.reverse, pattern in patterns.reverse do
          notAlt ← mkArrow (← mkEq discr pattern) notAlt
        notAlt ← mkForallFVars (discrs ++ ys) notAlt
        trace[Meta.debug] "notAlt: {notAlt}"
        let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ patterns ++ alts)
        let rhs := mkAppN alt rhsArgs
        let thmType ← mkEq lhs rhs
        let thmType ← hs.foldrM (init := thmType) mkArrow
        let thmType ← mkForallFVars (params ++ #[motive] ++ alts ++ ys) thmType
        let thmVal ← proveCondEqThm matchDeclName thmType
        trace[Meta.debug] "thmVal: {thmVal}"
        let thmName := matchDeclName ++ ((`eq).appendIndexAfter idx)
        addDecl <| Declaration.thmDecl {
          name        := thmName
          levelParams := constInfo.levelParams
          type        := thmType
          value       := thmVal
        }
        return (notAlt, splitterAltType)
      notAlts := notAlts.push notAlt
      splitterAltTypes := splitterAltTypes.push splitterAltType
      trace[Meta.Match.matchEqs] "splitterAltType: {splitterAltType}"
      idx := idx + 1
    -- Define splitter with conditional/refined alternatives
    withSplitterAlts splitterAltTypes fun altsNew => do
      let elimParams := params.toArray ++ #[motive] ++ discrs.toArray ++ altsNew
      let elimType ← mkForallFVars elimParams matchResultType
      trace[Meta.Match.matchEqs] "splitterType: {elimType}"
      let template ← mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ discrs ++ alts)
      let template ← deltaExpand template (. == constInfo.name)
      let elimVal ← mkLambdaFVars elimParams (← mkSplitterProof matchDeclName template alts altsNew)
      let elimName := matchDeclName ++ `elim
      addDecl <| Declaration.thmDecl {
        name        := elimName
        levelParams := constInfo.levelParams
        type        := elimType
        value       := elimVal
      }

builtin_initialize registerTraceClass `Meta.Match.matchEqs

end Lean.Meta.Match
