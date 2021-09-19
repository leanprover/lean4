/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.Match
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.SplitIf

namespace Lean.Meta

/--
  Helper method for `proveCondEqThm`. Given a goal of the form `C.rec ... xMajor = rhs`,
  apply `cases xMajor`. -/
partial def casesOnStuckLHS (mvarId : MVarId) : MetaM (Array MVarId) := do
  let target ← getMVarType mvarId
  if let some (_, lhs, rhs) ← matchEq? target then
    if let some fvarId ← findFVar? lhs then
      return (← cases mvarId fvarId).map fun s => s.mvarId
  throwError "'casesOnStuckLHS' failed"
where
  findFVar? (e : Expr) : MetaM (Option FVarId) := do
    match e with
    | Expr.proj _ _ e _ => findFVar? e
    | Expr.app .. =>
      let f := e.getAppFn
      if !f.isConst then
        return none
      else
        let declName := f.constName!
        let args := e.getAppArgs
        match (← getProjectionFnInfo? declName) with
        | some projInfo =>
          if projInfo.numParams < args.size then
            findFVar? args[projInfo.numParams]
          else
            return none
        | none =>
          matchConstRec e.getAppFn (fun _ => return none) fun recVal _ => do
            if recVal.getMajorIdx >= args.size then
              return none
            let major := args[recVal.getMajorIdx]
            if major.isFVar then
              return some major.fvarId!
            else
              return none
    | _ => return none

def casesOnStuckLHS? (mvarId : MVarId) : MetaM (Option (Array MVarId)) := do
  try casesOnStuckLHS mvarId catch _ => return none

namespace Match

structure MatchEqns where
  eqnNames             : Array Name
  splitterName         : Name
  splitterAltNumParams : Array Nat
  deriving Inhabited, Repr

structure MatchEqnsExtState where
  map : Std.PHashMap Name MatchEqns := {}
  deriving Inhabited

/- We generate the equations and splitter on demand, and do not save them on .olean files. -/
builtin_initialize matchEqnsExt : EnvExtension MatchEqnsExtState ←
  registerEnvExtension (pure {})

private def registerMatchEqns (matchDeclName : Name) (matchEqns : MatchEqns) : CoreM Unit :=
  modifyEnv fun env => matchEqnsExt.modifyState env fun s => { s with map := s.map.insert matchDeclName matchEqns }

/-- Create a "unique" base name for conditional equations and splitter -/
private def mkBaseNameFor (env : Environment) (matchDeclName : Name) : Name :=
  Lean.mkBaseNameFor env matchDeclName `splitter `_matchEqns

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

inductive InjectionAnyResult where
  | solved
  | failed
  | subgoal (mvarId : MVarId)

private def injenctionAny (mvarId : MVarId) : MetaM InjectionAnyResult :=
  withMVarContext mvarId do
    for localDecl in (← getLCtx) do
      if let some (_, lhs, rhs) ← matchEq? localDecl.type then
        unless (← isDefEq lhs rhs) do
          let lhs ← whnf lhs
          let rhs ← whnf rhs
          unless lhs.isNatLit && rhs.isNatLit do
            try
              match (← injection mvarId localDecl.fvarId) with
              | InjectionResult.solved  => return InjectionAnyResult.solved
              | InjectionResult.subgoal mvarId .. => return InjectionAnyResult.subgoal mvarId
            catch _ =>
              pure ()
    return InjectionAnyResult.failed

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
    proveSubgoal mvarId
  instantiateMVars proof
where
  mkMap : FVarIdMap Expr := do
    let mut m := {}
    for alt in alts, altNew in altsNew do
      m := m.insert alt.fvarId! altNew
    return m

  convertTemplate (m : FVarIdMap Expr) : StateRefT (Array MVarId) MetaM Expr :=
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

  proveSubgoalLoop (mvarId : MVarId) : MetaM Unit := do
    if (← contradictionCore mvarId {}) then
      return ()
    match (← injenctionAny mvarId) with
    | InjectionAnyResult.solved => return ()
    | InjectionAnyResult.failed => throwError "failed to generate splitter for match auxiliary declaration '{matchDeclName}', unsolved subgoal:\n{MessageData.ofGoal mvarId}"
    | InjectionAnyResult.subgoal mvarId => proveSubgoalLoop mvarId

  proveSubgoal (mvarId : MVarId) : MetaM Unit := do
    trace[Meta.Match.matchEqs] "subgoal {mkMVar mvarId}, {repr (← getMVarDecl mvarId).kind}, {← isExprMVarAssigned mvarId}\n{MessageData.ofGoal mvarId}"
    let (_, mvarId) ← intros mvarId
    let mvarId ← tryClearMany mvarId (alts.map (·.fvarId!))
    proveSubgoalLoop mvarId

/--
  Create conditional equations and splitter for the given match auxiliary declaration. -/
private partial def mkEquationsFor (matchDeclName : Name) :  MetaM MatchEqns := do
  let baseName := mkBaseNameFor (← getEnv) matchDeclName
  let constInfo ← getConstInfo matchDeclName
  let us := constInfo.levelParams.map mkLevelParam
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "'{matchDeclName}' is not a matcher function"
  forallTelescopeReducing constInfo.type fun xs matchResultType => do
    let mut eqnNames := #[]
    let params := xs[:matchInfo.numParams]
    let motive := xs[matchInfo.getMotivePos]
    let alts   := xs[xs.size - matchInfo.numAlts:]
    let firstDiscrIdx := matchInfo.numParams + 1
    let discrs := xs[firstDiscrIdx : firstDiscrIdx + matchInfo.numDiscrs]
    let mut notAlts := #[]
    let mut idx := 1
    let mut splitterAltTypes := #[]
    let mut splitterAltNumParams := #[]
    for alt in alts do
      let thmName := baseName ++ ((`eq).appendIndexAfter idx)
      eqnNames := eqnNames.push thmName
      let altType ← inferType alt
      let (notAlt, splitterAltType, splitterAltNumParam) ← forallTelescopeReducing altType fun ys altResultType => do
        let (ys, rhsArgs) ← toFVarsRHSArgs ys altResultType
        let patterns := altResultType.getAppArgs
        let mut hs := #[]
        for notAlt in notAlts do
          hs := hs.push (← instantiateForall notAlt patterns)
        hs ← simpHs hs patterns.size
        trace[Meta.Match.matchEqs] "hs: {hs}"
        let splitterAltType ← mkForallFVars ys (← hs.foldrM (init := altResultType) mkArrow)
        let splitterAltNumParam := hs.size + ys.size
        -- Create a proposition for representing terms that do not match `patterns`
        let mut notAlt := mkConst ``False
        for discr in discrs.toArray.reverse, pattern in patterns.reverse do
          notAlt ← mkArrow (← mkEq discr pattern) notAlt
        notAlt ← mkForallFVars (discrs ++ ys) notAlt
        let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ patterns ++ alts)
        let rhs := mkAppN alt rhsArgs
        let thmType ← mkEq lhs rhs
        let thmType ← hs.foldrM (init := thmType) mkArrow
        let thmType ← mkForallFVars (params ++ #[motive] ++ alts ++ ys) thmType
        let thmVal ← proveCondEqThm matchDeclName thmType
        addDecl <| Declaration.thmDecl {
          name        := thmName
          levelParams := constInfo.levelParams
          type        := thmType
          value       := thmVal
        }
        return (notAlt, splitterAltType, splitterAltNumParam)
      notAlts := notAlts.push notAlt
      splitterAltTypes := splitterAltTypes.push splitterAltType
      splitterAltNumParams := splitterAltNumParams.push splitterAltNumParam
      trace[Meta.Match.matchEqs] "splitterAltType: {splitterAltType}"
      idx := idx + 1
    -- Define splitter with conditional/refined alternatives
    withSplitterAlts splitterAltTypes fun altsNew => do
      let splitterParams := params.toArray ++ #[motive] ++ discrs.toArray ++ altsNew
      let splitterType ← mkForallFVars splitterParams matchResultType
      trace[Meta.Match.matchEqs] "splitterType: {splitterType}"
      let template ← mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ discrs ++ alts)
      let template ← deltaExpand template (. == constInfo.name)
      let splitterVal ← mkLambdaFVars splitterParams (← mkSplitterProof matchDeclName template alts altsNew)
      let splitterName := baseName ++ `splitter
      addDecl <| Declaration.thmDecl {
        name        := splitterName
        levelParams := constInfo.levelParams
        type        := splitterType
        value       := splitterVal
      }
      let result := { eqnNames, splitterName, splitterAltNumParams }
      registerMatchEqns matchDeclName result
      return result

def getEquationsFor (matchDeclName : Name) : MetaM MatchEqns := do
  match matchEqnsExt.getState (← getEnv) |>.map.find? matchDeclName with
  | some matchEqns => return matchEqns
  | none => mkEquationsFor matchDeclName

builtin_initialize registerTraceClass `Meta.Match.matchEqs

end Lean.Meta.Match
