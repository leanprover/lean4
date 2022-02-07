/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.Match
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Tactic.Injection
import Lean.Meta.Tactic.Contradiction

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
    match e.getAppFn with
    | Expr.proj _ _ e _ => findFVar? e
    | f =>
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
          matchConstRec f (fun _ => return none) fun recVal _ => do
            if recVal.getMajorIdx >= args.size then
              return none
            let major := args[recVal.getMajorIdx]
            if major.isFVar then
              return some major.fvarId!
            else
              return none

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

def unfoldNamedPattern (e : Expr) : MetaM Expr := do
  let visit (e : Expr) : MetaM TransformStep := do
    if e.isAppOfArity ``namedPattern 4 then
      if let some eNew ← unfoldDefinition? e then
        return TransformStep.visit eNew
    return TransformStep.visit e
  Meta.transform e (pre := visit)

/--
  Similar to `forallTelescopeReducing`, but eliminates arguments for named parameters and the associated
  equation proofs. The continuation `k` takes four arguments `ys args mask type`.
  - `ys` are variables for the hypotheses that have not been eliminated.
  - `args` are the arguments for the alternative `alt` that has type `altType`. `ys.size <= args.size`
  - `mask[i]` is true if the hypotheses has not been eliminated. `mask.size == args.size`.
  - `type` is the resulting type for `altType`.

  We use the `mask` to build the splitter proof. See `mkSplitterProof`.
-/
partial def forallAltTelescope (altType : Expr) (k : Array Expr → Array Expr → Array Bool → Expr → MetaM α) : MetaM α := do
  go #[] #[] #[] altType
where
  go (ys : Array Expr) (args : Array Expr) (mask : Array Bool) (type : Expr) : MetaM α := do
    let type ← whnfForall type
    match type with
    | Expr.forallE n d b .. =>
      let d ← unfoldNamedPattern d
      withLocalDeclD n d fun y => do
        let typeNew := b.instantiate1 y
        if let some (_, lhs, rhs) ← matchEq? d then
          if lhs.isFVar && ys.contains lhs && args.contains lhs && isNamedPatternProof typeNew y then
             let some i  := ys.getIdx? lhs | unreachable!
             let ys      := ys.eraseIdx i
             let mask    := mask.set! i false
             let args    := args.map fun arg => if arg == lhs then rhs else arg
             let args    := args.push (← mkEqRefl rhs)
             let typeNew := typeNew.replaceFVar lhs rhs
             return (← go ys args (mask.push false) typeNew)
        go (ys.push y) (args.push y) (mask.push true) typeNew
    | _ =>
      let type ← unfoldNamedPattern type
      /- Recall that alternatives that do not have variables have a `Unit` parameter to ensure
         they are not eagerly evaluated. -/
      if ys.size == 1 then
        if (← inferType ys[0]).isConstOf ``Unit && !(← dependsOn type ys[0].fvarId!) then
          return (← k #[] #[mkConst ``Unit.unit] #[false] type)
      k ys args mask type

  isNamedPatternProof (type : Expr) (h : Expr) : Bool :=
    Option.isSome <| type.find? fun e =>
      e.isAppOfArity ``namedPattern 4 && e.appArg! == h

namespace SimpH

/--
  State for the equational theorem hypothesis simplifier.

  Recall that each equation contains additional hypotheses to ensure the associated case does not taken by previous cases.
  We have one hypothesis for each previous case.

  Each hypothesis is of the form `forall xs, eqs → False`

  We use tactics to minimize code duplication.
-/
structure State where
  mvarId : MVarId            -- Goal representing the hypothesis
  xs  : List FVarId          -- Pattern variables for a previous case
  eqs : List FVarId          -- Equations to be processed
  eqsNew : List FVarId := [] -- Simplied (already processed) equations

abbrev M := StateRefT State MetaM

/--
  Apply the given substitution to `fvarIds`.
  This is an auxiliary method for `substRHS`.
-/
private def applySubst (s : FVarSubst) (fvarIds : List FVarId) : List FVarId :=
  fvarIds.filterMap fun fvarId => match s.apply (mkFVar fvarId) with
    | Expr.fvar fvarId .. => some fvarId
    | _ => none

/--
  Given an equation of the form `lhs = rhs` where `rhs` is variable in `xs`,
  the replace it everywhere with `lhs`.
-/
private def substRHS (eq : FVarId) (rhs : FVarId) : M Unit := do
  assert! (← get).xs.contains rhs
  let (subst, mvarId) ← substCore (← get).mvarId eq (symm := true)
  modify fun s => { s with
    mvarId,
    xs  := applySubst subst (s.xs.erase rhs)
    eqs := applySubst subst s.eqs
    eqsNew := applySubst subst s.eqsNew
  }

private def isDone : M Bool :=
  return (← get).eqs.isEmpty

/--
  Auxiliary tactic that tries to replace as many variables as possible and then apply `contradiction`.
  We use it to discard redundant hypotheses.
-/
private def trySubstVarsAndContradiction (mvarId : MVarId) : MetaM Bool :=
  commitWhen do
    let mvarId ← substVars mvarId
    contradictionCore mvarId {}

private def processNextEq : M Bool := do
  let s ← get
  withMVarContext s.mvarId do
    -- If the goal is contradictory, the hypothesis is redundant.
    if (← contradictionCore s.mvarId {}) then
      return false
    if let eq :: eqs := s.eqs then
      modify fun s => { s with eqs }
      let eqType ← inferType (mkFVar eq)
      -- See `substRHS`. Recall that if `rhs` is a variable then if must be in `s.xs`
      if let some (_, lhs, rhs) ← matchEq? eqType then
        if rhs.isFVar then
          substRHS eq rhs.fvarId!
          return true
      if let some (α, lhs, β, rhs) ← matchHEq? eqType then
        -- Try to convert `HEq` into `Eq`
        if (← isDefEq α β) then
          let (eqNew, mvarId) ← heqToEq s.mvarId eq (tryToClear := true)
          modify fun s => { s with mvarId, eqs := eqNew :: s.eqs }
          return true
        -- If it is not possible, we try to show the hypothesis is redundant by substituting even variables that are not at `s.xs`, and then use contradiction.
        else if (← trySubstVarsAndContradiction s.mvarId) then
          return false
      try
        -- Try to simplify equation using `injection` tactic.
        match (← injection s.mvarId eq) with
        | InjectionResult.solved => return false
        | InjectionResult.subgoal mvarId eqNews .. =>
          modify fun s => { s with mvarId, eqs := eqNews.toList ++ s.eqs }
      catch _ =>
        modify fun s => { s with eqsNew := eq :: s.eqsNew }
    return true

partial def go : M Bool := do
  if (← isDone) then
    return true
  else if (← processNextEq) then
    go
  else
    return false

end SimpH

/--
  Auxiliary method for simplifying equational theorem hypotheses.

  Recall that each equation contains additional hypotheses to ensure the associated case does not taken by previous cases.
  We have one hypothesis for each previous case.
-/
private partial def simpH? (h : Expr) (numEqs : Nat) : MetaM (Option Expr) := withDefault do
  let numVars ← forallTelescope h fun ys _ => pure (ys.size - numEqs)
  let mvarId := (← mkFreshExprSyntheticOpaqueMVar h).mvarId!
  let (xs, mvarId) ← introN mvarId numVars
  let (eqs, mvarId) ← introN mvarId numEqs
  let (r, s) ← SimpH.go |>.run { mvarId, xs := xs.toList, eqs := eqs.toList }
  if r then
    withMVarContext s.mvarId do
      let vars := (s.xs ++ s.eqsNew.reverse).toArray.map mkFVar
      let r ← mkForallFVars vars (mkConst ``False)
      trace[Meta.Match.matchEqs] "simplified hypothesis{indentExpr r}"
      check r
      return some r
  else
    return none

private def substSomeVar (mvarId : MVarId) : MetaM (Array MVarId) := withMVarContext mvarId do
  for localDecl in (← getLCtx) do
    if let some (_, lhs, rhs) ← matchEq? localDecl.type then
      if lhs.isFVar then
        if !(← dependsOn rhs lhs.fvarId!) then
          match (← subst? mvarId lhs.fvarId!) with
          | some mvarId => return #[mvarId]
          | none => pure ()
  throwError "substSomeVar failed"

/--
  Helper method for proving a conditional equational theorem associated with an alternative of
  the `match`-eliminator `matchDeclName`. `type` contains the type of the theorem. -/
partial def proveCondEqThm (matchDeclName : Name) (type : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  withLCtx {} {} <| forallTelescope type fun ys target => do
    let mvar0  ← mkFreshExprSyntheticOpaqueMVar target
    let mvarId ← deltaTarget mvar0.mvarId! (. == matchDeclName)
    trace[Meta.Match.matchEqs] "{MessageData.ofGoal mvarId}"
    withDefault <| go mvarId 0
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
      (substSomeVar mvarId)
      <|>
      (throwError "failed to generate equality theorems for `match` expression\n{MessageData.ofGoal mvarId}")
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
private partial def mkSplitterProof (matchDeclName : Name) (template : Expr) (alts altsNew : Array Expr)
    (altArgMasks : Array (Array Bool)) : MetaM Expr := do
  trace[Meta.Match.matchEqs] "proof template: {template}"
  let map := mkMap
  let (proof, mvarIds) ← convertTemplate map |>.run #[]
  trace[Meta.Match.matchEqs] "splitter proof: {proof}"
  for mvarId in mvarIds do
    proveSubgoal mvarId
  instantiateMVars proof
where
  mkMap : FVarIdMap (Expr × Array Bool) := Id.run <| do
    let mut m := {}
    for alt in alts, altNew in altsNew, argMask in altArgMasks do
      m := m.insert alt.fvarId! (altNew, argMask)
    return m

  convertTemplate (m : FVarIdMap (Expr × Array Bool)) : StateRefT (Array MVarId) MetaM Expr :=
    transform template fun e => do
      match e.getAppFn with
      | Expr.fvar fvarId .. =>
        match m.find? fvarId with
        | some (altNew, argMask) =>
          trace[Meta.Match.matchEqs] ">> {e}, {altNew}"
          let mut newArgs := #[]
          for arg in e.getAppArgs, includeArg in argMask do
            if includeArg then
              newArgs := newArgs.push arg
          let eNew := mkAppN altNew newArgs
          let (mvars, _, _) ← forallMetaTelescopeReducing (← inferType eNew) (kind := MetavarKind.syntheticOpaque)
          modify fun s => s ++ (mvars.map (·.mvarId!))
          let eNew := mkAppN eNew mvars
          return TransformStep.done eNew
        | none => return TransformStep.visit e
      | _ => return TransformStep.visit e

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
private partial def mkEquationsFor (matchDeclName : Name) :  MetaM MatchEqns :=
  withConfig (fun c => { c with etaStruct := false }) do
  let baseName := mkPrivateName (← getEnv) matchDeclName
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
    let mut altArgMasks := #[] -- masks produced by `forallAltTelescope`
    for alt in alts do
      let thmName := baseName ++ ((`eq).appendIndexAfter idx)
      eqnNames := eqnNames.push thmName
      let (notAlt, splitterAltType, splitterAltNumParam, argMask) ← forallAltTelescope (← inferType alt) fun ys rhsArgs argMask altResultType => do
        let patterns := altResultType.getAppArgs
        let mut hs := #[]
        for notAlt in notAlts do
          let h ← instantiateForall notAlt patterns
          if let some h ← simpH? h patterns.size then
            hs := hs.push h
        trace[Meta.Match.matchEqs] "hs: {hs}"
        let splitterAltType ← mkForallFVars ys (← hs.foldrM (init := altResultType) mkArrow)
        let splitterAltNumParam := hs.size + ys.size
        -- Create a proposition for representing terms that do not match `patterns`
        let mut notAlt := mkConst ``False
        for discr in discrs.toArray.reverse, pattern in patterns.reverse do
          if (← isDefEq (← inferType discr) (← inferType pattern)) then
            notAlt ← mkArrow (← mkEq discr pattern) notAlt
          else
            notAlt ← mkArrow (← mkHEq discr pattern) notAlt
        notAlt ← mkForallFVars (discrs ++ ys) notAlt
        let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ patterns ++ alts)
        let rhs := mkAppN alt rhsArgs
        let thmType ← mkEq lhs rhs
        let thmType ← hs.foldrM (init := thmType) mkArrow
        let thmType ← mkForallFVars (params ++ #[motive] ++ alts ++ ys) thmType
        let thmType ← unfoldNamedPattern thmType
        let thmVal ← proveCondEqThm matchDeclName thmType
        addDecl <| Declaration.thmDecl {
          name        := thmName
          levelParams := constInfo.levelParams
          type        := thmType
          value       := thmVal
        }
        return (notAlt, splitterAltType, splitterAltNumParam, argMask)
      notAlts := notAlts.push notAlt
      splitterAltTypes := splitterAltTypes.push splitterAltType
      splitterAltNumParams := splitterAltNumParams.push splitterAltNumParam
      altArgMasks := altArgMasks.push argMask
      trace[Meta.Match.matchEqs] "splitterAltType: {splitterAltType}"
      idx := idx + 1
    -- Define splitter with conditional/refined alternatives
    withSplitterAlts splitterAltTypes fun altsNew => do
      let splitterParams := params.toArray ++ #[motive] ++ discrs.toArray ++ altsNew
      let splitterType ← mkForallFVars splitterParams matchResultType
      trace[Meta.Match.matchEqs] "splitterType: {splitterType}"
      let template := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ discrs ++ alts)
      let template ← deltaExpand template (. == constInfo.name)
      let splitterVal ← mkLambdaFVars splitterParams (← mkSplitterProof matchDeclName template alts altsNew altArgMasks)
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
