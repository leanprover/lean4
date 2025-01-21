/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Util.CollectFVars
import Lean.AuxRecursor
import Lean.Parser.Term
import Lean.Meta.RecursorInfo
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.ElimInfo
import Lean.Meta.Tactic.Induction
import Lean.Meta.Tactic.Cases
import Lean.Meta.GeneralizeVars
import Lean.Elab.App
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Generalize

namespace Lean.Elab.Tactic
open Meta

/-
  Given an `inductionAlt` of the form
  ```
  syntax inductionAltLHS := "| " (group("@"? ident) <|> hole) (ident <|> hole)*
  syntax inductionAlt  := ppDedent(ppLine) inductionAltLHS+ " => " (hole <|> syntheticHole <|> tacticSeq)
  ```
-/
private def getAltLhses (alt : Syntax) : Syntax :=
  alt[0]
private def getFirstAltLhs (alt : Syntax) : Syntax :=
  (getAltLhses alt)[0]
/-- Return `inductionAlt` name. It assumes `alt` does not have multiple `inductionAltLHS` -/
private def getAltName (alt : Syntax) : Name :=
  let lhs := getFirstAltLhs alt
  if !lhs[1].isOfKind ``Parser.Term.hole then lhs[1][1].getId.eraseMacroScopes else `_
/-- Returns the `inductionAlt` `ident <|> hole` -/
private def getAltNameStx (alt : Syntax) : Syntax :=
  let lhs := getFirstAltLhs alt
  if lhs[1].isOfKind ``Parser.Term.hole then lhs[1] else lhs[1][1]
/-- Return `true` if the first LHS of the given alternative contains `@`. -/
private def altHasExplicitModifier (alt : Syntax) : Bool :=
  let lhs := getFirstAltLhs alt
  !lhs[1].isOfKind ``Parser.Term.hole && !lhs[1][0].isNone
/-- Return the variables in the first LHS of the given alternative. -/
private def getAltVars (alt : Syntax) : Array Syntax :=
  let lhs := getFirstAltLhs alt
  lhs[2].getArgs
private def getAltRHS (alt : Syntax) : Syntax :=
  alt[2]
private def getAltDArrow (alt : Syntax) : Syntax :=
  alt[1]

-- Return true if `stx` is a term occurring in the RHS of the induction/cases tactic
def isHoleRHS (rhs : Syntax) : Bool :=
  rhs.isOfKind ``Parser.Term.syntheticHole || rhs.isOfKind ``Parser.Term.hole

def evalAlt (mvarId : MVarId) (alt : Syntax) (addInfo : TermElabM Unit) : TacticM Unit :=
  let rhs := getAltRHS alt
  withCaseRef (getAltDArrow alt) rhs do
    if isHoleRHS rhs then
      addInfo
      mvarId.withContext <| withTacticInfoContext rhs do
        let mvarDecl ← mvarId.getDecl
        let val ← elabTermEnsuringType rhs mvarDecl.type
        mvarId.assign val
        let gs' ← getMVarsNoDelayed val
        tagUntaggedGoals mvarDecl.userName `induction gs'.toList
        setGoals <| (← getGoals) ++ gs'.toList
    else
      let goals ← getGoals
      try
        setGoals [mvarId]
        closeUsingOrAdmit <|
          withTacticInfoContext (mkNullNode #[getAltLhses alt, getAltDArrow alt]) <|
            (addInfo *> evalTactic rhs)
      finally
        setGoals goals

/-!
  Helper method for creating an user-defined eliminator/recursor application.
-/
namespace ElimApp

structure Alt where
  /-- The short name of the alternative, used in `| foo =>` cases -/
  name      : Name
  info      : ElimAltInfo
  /-- The subgoal metavariable for the alternative. -/
  mvarId    : MVarId
  deriving Inhabited

structure Context where
  elimInfo : ElimInfo
  targets  : Array Expr -- targets provided by the user

structure State where
  argPos    : Nat := 0 -- current argument position
  targetPos : Nat := 0 -- current target at targetsStx
  motive    : Option MVarId -- motive metavariable
  f         : Expr
  fType     : Expr
  alts      : Array Alt := #[]
  insts     : Array MVarId := #[]

abbrev M := ReaderT Context $ StateRefT State TermElabM

private def addNewArg (arg : Expr) : M Unit :=
  modify fun s => { s with argPos := s.argPos+1, f := mkApp s.f arg, fType := s.fType.bindingBody!.instantiate1 arg }

/-- Return the binder name at `fType`. This method assumes `fType` is a function type. -/
private def getBindingName : M Name := return (← get).fType.bindingName!
/-- Return the next argument expected type. This method assumes `fType` is a function type. -/
private def getArgExpectedType : M Expr := return (← get).fType.bindingDomain!

private def getFType : M Expr := do
  let fType ← whnfForall (← get).fType
  modify fun s => { s with fType := fType }
  pure fType

structure Result where
  elimApp : Expr
  motive  : MVarId
  alts    : Array Alt := #[]
  others  : Array MVarId := #[]

/--
  Construct the an eliminator/recursor application. `targets` contains the explicit and implicit targets for
  the eliminator. For example, the indices of builtin recursors are considered implicit targets.
  Remark: the method `addImplicitTargets` may be used to compute the sequence of implicit and explicit targets
  from the explicit ones.
-/
partial def mkElimApp (elimInfo : ElimInfo) (targets : Array Expr) (tag : Name) : TermElabM Result := do
  let rec loop : M Unit := do
    match (← getFType) with
    | .forallE binderName _ _ c =>
      let ctx ← read
      let argPos := (← get).argPos
      if ctx.elimInfo.motivePos == argPos then
        let motive ← mkFreshExprMVar (← getArgExpectedType) MetavarKind.syntheticOpaque
        modify fun s => { s with motive := motive.mvarId! }
        addNewArg motive
      else if ctx.elimInfo.targetsPos.contains argPos then
        let s ← get
        let ctx ← read
        unless s.targetPos < ctx.targets.size do
          throwError "insufficient number of targets for '{elimInfo.elimExpr}'"
        let target := ctx.targets[s.targetPos]!
        let expectedType ← getArgExpectedType
        let target ← withAssignableSyntheticOpaque <| Term.ensureHasType expectedType target
        modify fun s => { s with targetPos := s.targetPos + 1 }
        addNewArg target
      else match c with
        | .implicit =>
          let arg ← mkFreshExprMVar (← getArgExpectedType)
          addNewArg arg
        | .strictImplicit =>
          let arg ← mkFreshExprMVar (← getArgExpectedType)
          addNewArg arg
        | .instImplicit =>
          let arg ← mkFreshExprMVar (← getArgExpectedType) (kind := MetavarKind.synthetic) (userName := appendTag tag binderName)
          modify fun s => { s with insts := s.insts.push arg.mvarId! }
          addNewArg arg
        | _ =>
          let arg ← mkFreshExprSyntheticOpaqueMVar (← getArgExpectedType) (tag := appendTag tag binderName)
          let x   ← getBindingName
          modify fun s =>
            let info := elimInfo.altsInfo[s.alts.size]!
            { s with alts := s.alts.push ⟨x, info, arg.mvarId!⟩ }
          addNewArg arg
      loop
    | _ =>
      pure ()
  let (_, s) ← (loop).run { elimInfo := elimInfo, targets := targets }
    |>.run { f := elimInfo.elimExpr, fType := elimInfo.elimType, motive := none }
  let mut others := #[]
  for mvarId in s.insts do
    try
      unless (← Term.synthesizeInstMVarCore mvarId) do
        mvarId.setKind .syntheticOpaque
        others := others.push mvarId
    catch _ =>
      mvarId.setKind .syntheticOpaque
      others := others.push mvarId
  let alts ← s.alts.filterM fun alt => return !(← alt.mvarId.isAssigned)
  let some motive := s.motive |
      throwError "mkElimApp: motive not found"
  return { elimApp := (← instantiateMVars s.f), alts, others, motive }

/-- Given a goal `... targets ... |- C[targets]` associated with `mvarId`, assign
  `motiveArg := fun targets => C[targets]` -/
def setMotiveArg (mvarId : MVarId) (motiveArg : MVarId) (targets : Array FVarId) : MetaM Unit := do
  let type ← inferType (mkMVar mvarId)
  let motive ← mkLambdaFVars (targets.map mkFVar) type
  let motiverInferredType ← inferType motive
  let motiveType ← inferType (mkMVar motiveArg)
  unless (← isDefEqGuarded motiverInferredType motiveType) do
    throwError "type mismatch when assigning motive{indentExpr motive}\n{← mkHasTypeButIsExpectedMsg motiverInferredType motiveType}"
  motiveArg.assign motive

private def getAltNumFields (elimInfo : ElimInfo) (altName : Name) : TermElabM Nat := do
  for altInfo in elimInfo.altsInfo do
    if altInfo.name == altName then
      return altInfo.numFields
  throwError "unknown alternative name '{altName}'"

private def isWildcard (altStx : Syntax) : Bool :=
  getAltName altStx == `_

private def checkAltNames (alts : Array Alt) (altsSyntax : Array Syntax) : TacticM Unit := do
  let mut seenNames : Array Name := #[]
  for h : i in [:altsSyntax.size] do
    let altStx := altsSyntax[i]
    if getAltName altStx == `_ && i != altsSyntax.size - 1 then
      withRef altStx <| throwError "invalid occurrence of wildcard alternative, it must be the last alternative"
    let altName := getAltName altStx
    if altName != `_ then
      if seenNames.contains altName then
        throwErrorAt altStx s!"duplicate alternative name '{altName}'"
      seenNames := seenNames.push altName
      unless alts.any (·.name == altName) do
        let unhandledAlts := alts.filter fun alt => !seenNames.contains alt.name
        let msg :=
          if unhandledAlts.isEmpty then
            m!"invalid alternative name '{altName}', no unhandled alternatives"
          else
            let unhandledAltsMessages := unhandledAlts.map (m!"{·.name}")
            let unhandledAlts := MessageData.orList unhandledAltsMessages.toList
            m!"invalid alternative name '{altName}', expected {unhandledAlts}"
        throwErrorAt altStx msg


/-- Given the goal `altMVarId` for a given alternative that introduces `numFields` new variables,
    return the number of explicit variables. Recall that when the `@` is not used, only the explicit variables can
    be named by the user. -/
private def getNumExplicitFields (altMVarId : MVarId) (numFields : Nat) : MetaM Nat := altMVarId.withContext do
  let target ← altMVarId.getType
  withoutModifyingState do
    -- The `numFields` count includes explicit, implicit and let-bound variables.
    -- `forallMetaBoundTelescope` will reduce let-bindings, so we don't just count how many
    -- explicit binders are in `bis`, but how many implicit ones.
    -- If this turns out to be insufficient, then the real (and complicated) logic for which
    -- arguments are explicit or implicit can be found in  `introNImp`,
    let (_, bis, _) ← forallMetaBoundedTelescope target numFields
    let numImplicits := (bis.filter (!·.isExplicit)).size
    return numFields - numImplicits

private def saveAltVarsInfo (altMVarId : MVarId) (altStx : Syntax) (fvarIds : Array FVarId) : TermElabM Unit :=
  withSaveInfoContext <| altMVarId.withContext do
    let useNamesForExplicitOnly := !altHasExplicitModifier altStx
    let mut i := 0
    let altVars := getAltVars altStx
    for fvarId in fvarIds do
      if !useNamesForExplicitOnly || (← fvarId.getDecl).binderInfo.isExplicit then
        if h : i < altVars.size then
          Term.addLocalVarInfo altVars[i] (mkFVar fvarId)
          i := i + 1

open Language in
def evalAlts (elimInfo : ElimInfo) (alts : Array Alt) (optPreTac : Syntax) (altStxs : Array Syntax)
    (initialInfo : Info)
    (numEqs : Nat := 0) (numGeneralized : Nat := 0) (toClear : Array FVarId := #[])
    (toTag : Array (Ident × FVarId) := #[]) : TacticM Unit := do
  let hasAlts := altStxs.size > 0
  if hasAlts then
    -- default to initial state outside of alts
    -- HACK: because this node has the same span as the original tactic,
    -- we need to take all the info trees we have produced so far and re-nest them
    -- inside this node as well
    let treesSaved ← getResetInfoTrees
    withInfoContext ((modifyInfoState fun s => { s with trees := treesSaved }) *> goWithInfo) (pure initialInfo)
  else goWithInfo
where
  -- continuation in the correct info context
  goWithInfo := do
    let hasAlts := altStxs.size > 0

    if hasAlts then
      if let some tacSnap := (← readThe Term.Context).tacSnap? then
        -- incrementality: create a new promise for each alternative, resolve current snapshot to
        -- them, eventually put each of them back in `Context.tacSnap?` in `applyAltStx`
        withAlwaysResolvedPromise fun finished => do
          withAlwaysResolvedPromises altStxs.size fun altPromises => do
            tacSnap.new.resolve {
              -- save all relevant syntax here for comparison with next document version
              stx := mkNullNode altStxs
              diagnostics := .empty
              inner? := none
              finished := { range? := none, task := finished.result }
              next := altStxs.zipWith altPromises fun stx prom =>
                { range? := stx.getRange?, task := prom.result }
            }
            goWithIncremental <| altPromises.mapIdx fun i prom => {
              old? := do
                let old ← tacSnap.old?
                -- waiting is fine here: this is the old version of the snapshot resolved above
                -- immediately at the beginning of the tactic
                let old := old.val.get
                -- use old version of `mkNullNode altsSyntax` as guard, will be compared with new
                -- version and picked apart in `applyAltStx`
                return ⟨old.stx, (← old.next[i]?)⟩
              new := prom
            }
            finished.resolve { diagnostics := .empty, state? := (← saveState) }
        return

    goWithIncremental #[]

  -- continuation in the correct incrementality context
  goWithIncremental (tacSnaps : Array (SnapshotBundle TacticParsedSnapshot)) := do
    let hasAlts := altStxs.size > 0
    let mut alts := alts

    -- initial sanity checks: named cases should be known, wildcards should be last
    checkAltNames alts altStxs

    /-
    First process `altsSyntax` in order, removing covered alternatives from `alts`. Previously we
    did one loop through `alts`, looking up suitable alternatives from `altsSyntax`.
    Motivations for the change:

    1- It improves the effectiveness of incremental reuse. Consider the following example:
    ```lean
    example (h₁ : p ∨ q) (h₂ : p → x = 0) (h₃ : q → y = 0) : x * y = 0 := by
      cases h₁ with
      | inr h =>
        sleep 5000 -- sleeps for 5 seconds
        save
        have : y = 0 := h₃ h
        -- We can comfortably work here
      | inl h => stop ...
    ```
    If we iterated through `alts` instead of `altsSyntax`, the `inl` alternative would be executed
    first, making partial reuse in `inr` impossible (without support for reuse with position
    adjustments).

    2- The errors are produced in the same order the appear in the code above. This is not super
    important when using IDEs.
    -/
    for h : altStxIdx in [0:altStxs.size] do
      let altStx := altStxs[altStxIdx]
      let altName := getAltName altStx
      if let some i := alts.findFinIdx? (·.1 == altName) then
        -- cover named alternative
        applyAltStx tacSnaps altStxIdx altStx alts[i]
        alts := alts.eraseIdx i
      else if !alts.isEmpty && isWildcard altStx then
        -- cover all alternatives
        for alt in alts do
          applyAltStx tacSnaps altStxIdx altStx alt
        alts := #[]
      else
        throwErrorAt altStx "unused alternative '{altName}'"

    -- now process remaining alternatives; these might either be unreachable or we're in `induction`
    -- without `with`. In all other cases, remaining alternatives are flagged as errors.
    for { name := altName, info, mvarId := altMVarId } in alts do
      let numFields ← getAltNumFields elimInfo altName
      let mut (_, altMVarId) ← altMVarId.introN numFields
      let some (altMVarId', subst) ← Cases.unifyEqs? numEqs altMVarId {}
        | continue  -- alternative is not reachable
      altMVarId ← if info.provesMotive then
        (_, altMVarId) ← altMVarId'.introNP numGeneralized
        pure altMVarId
      else
        pure altMVarId'
      for fvarId in toClear do
        altMVarId ← altMVarId.tryClear fvarId
      altMVarId.withContext do
        for (stx, fvar) in toTag do
          Term.addLocalVarInfo stx (subst.get fvar)
      let altMVarIds ← applyPreTac altMVarId
      if !hasAlts then
        -- User did not provide alternatives using `|`
        setGoals <| (← getGoals) ++ altMVarIds
      else if !altMVarIds.isEmpty then
        logError m!"alternative '{altName}' has not been provided"
        altMVarIds.forM fun mvarId => admitGoal mvarId

  /-- Applies syntactic alternative to alternative goal. -/
  applyAltStx tacSnaps altStxIdx altStx alt := withRef altStx do
    let { name := altName, info, mvarId := altMVarId } := alt
    -- also checks for unknown alternatives
    let numFields ← getAltNumFields elimInfo altName
    let altVars := getAltVars altStx
    let numFieldsToName ← if altHasExplicitModifier altStx then pure numFields else getNumExplicitFields altMVarId numFields
    if altVars.size > numFieldsToName then
      logError m!"too many variable names provided at alternative '{altName}', #{altVars.size} provided, but #{numFieldsToName} expected"
    let mut (fvarIds, altMVarId) ← altMVarId.introN numFields (altVars.toList.map getNameOfIdent') (useNamesForExplicitOnly := !altHasExplicitModifier altStx)
    -- Delay adding the infos for the pattern LHS because we want them to nest
    -- inside tacticInfo for the current alternative (in `evalAlt`)
    let addInfo : TermElabM Unit := do
      if (← getInfoState).enabled then
        if let some declName := info.declName? then
          addConstInfo (getAltNameStx altStx) declName
        saveAltVarsInfo altMVarId altStx fvarIds
    let unusedAlt := do
      addInfo
      if !isWildcard altStx then
        throwError "alternative '{altName}' is not needed"
    let some (altMVarId', subst) ← Cases.unifyEqs? numEqs altMVarId {}
      | unusedAlt
    altMVarId ← if info.provesMotive then
      (_, altMVarId) ← altMVarId'.introNP numGeneralized
      pure altMVarId
    else
      pure altMVarId'
    for fvarId in toClear do
      altMVarId ← altMVarId.tryClear fvarId
    altMVarId.withContext do
      for (stx, fvar) in toTag do
        Term.addLocalVarInfo stx (subst.get fvar)
    let altMVarIds ← applyPreTac altMVarId
    if altMVarIds.isEmpty then
      return (← unusedAlt)

    -- select corresponding snapshot bundle for incrementality of this alternative
    -- note that `tacSnaps[altStxIdx]?` is `none` if `tacSnap?` was `none` to begin with
    withTheReader Term.Context ({ · with tacSnap? := tacSnaps[altStxIdx]? }) do
    -- all previous alternatives have to be unchanged for reuse
    Term.withNarrowedArgTacticReuse (stx := mkNullNode altStxs) (argIdx := altStxIdx) fun altStx => do
    -- everything up to rhs has to be unchanged for reuse
    Term.withNarrowedArgTacticReuse (stx := altStx) (argIdx := 2) fun _rhs => do
    -- disable reuse if rhs is run multiple times
    Term.withoutTacticIncrementality (altMVarIds.length != 1 || isWildcard altStx) do
      for altMVarId' in altMVarIds do
        evalAlt altMVarId' altStx addInfo

  /-- Applies `induction .. with $preTac | ..`, if any, to an alternative goal. -/
  applyPreTac (mvarId : MVarId) : TacticM (List MVarId) :=
    if optPreTac.isNone then
      return [mvarId]
    else
      -- disable incrementality for the pre-tactic to avoid non-monotonic progress reporting; it
      -- would be possible to include a custom task around the pre-tac with an appropriate range in
      -- the snapshot such that it is cached as well if it turns out that this is valuable
      Term.withoutTacticIncrementality true do
        evalTacticAt optPreTac[0] mvarId

end ElimApp

/-
  Recall that
  ```
  generalizingVars := optional (" generalizing " >> many1 ident)
  «induction»  := leading_parser nonReservedSymbol "induction " >> majorPremise >> usingRec >> generalizingVars >> optional inductionAlts
  ```
  `stx` is syntax for `induction`. -/
private def getUserGeneralizingFVarIds (stx : Syntax) : TacticM (Array FVarId) :=
  withRef stx do
    let generalizingStx := stx[3]
    if generalizingStx.isNone then
      pure #[]
    else
      trace[Elab.induction] "{generalizingStx}"
      let vars := generalizingStx[1].getArgs
      getFVarIds vars

-- process `generalizingVars` subterm of induction Syntax `stx`.
private def generalizeVars (mvarId : MVarId) (stx : Syntax) (targets : Array Expr) : TacticM (Nat × MVarId) :=
  mvarId.withContext do
    let userFVarIds ← getUserGeneralizingFVarIds stx
    let forbidden ← mkGeneralizationForbiddenSet targets
    let mut s ← getFVarSetToGeneralize targets forbidden
    for userFVarId in userFVarIds do
      if forbidden.contains userFVarId then
        throwError "variable cannot be generalized because target depends on it{indentExpr (mkFVar userFVarId)}"
      if s.contains userFVarId then
        throwError "unnecessary 'generalizing' argument, variable '{mkFVar userFVarId}' is generalized automatically"
      s := s.insert userFVarId
    let fvarIds ← sortFVarIds s.toArray
    let (fvarIds, mvarId') ← mvarId.revert fvarIds
    return (fvarIds.size, mvarId')

/--
Given `inductionAlts` of the form
```
syntax inductionAlts := "with " (tactic)? withPosition( (colGe inductionAlt)+)
```
Return an array containing its alternatives.
-/
private def getAltsOfInductionAlts (inductionAlts : Syntax) : Array Syntax :=
  inductionAlts[2].getArgs

/--
Given `inductionAlts` of the form
```
syntax inductionAlts := "with " (tactic)? withPosition( (colGe inductionAlt)+)
```
runs `cont alts` where `alts` is an array containing all `inductionAlt`s while disabling incremental
reuse if any other syntax changed.
-/
private def withAltsOfOptInductionAlts (optInductionAlts : Syntax)
    (cont : Array Syntax → TacticM α) : TacticM α :=
  Term.withNarrowedTacticReuse (stx := optInductionAlts) (fun optInductionAlts =>
    if optInductionAlts.isNone then
      -- if there are no alternatives, what to compare is irrelevant as there will be no reuse
      (mkNullNode #[], mkNullNode #[])
    else
      -- `with` and tactic applied to all branches must be unchanged for reuse
      (mkNullNode optInductionAlts[0].getArgs[:2], optInductionAlts[0].getArg 2))
    (fun alts => cont alts.getArgs)

private def getOptPreTacOfOptInductionAlts (optInductionAlts : Syntax) : Syntax :=
  if optInductionAlts.isNone then mkNullNode else optInductionAlts[0][1]

private def isMultiAlt (alt : Syntax) : Bool :=
  alt[0].getNumArgs > 1

/-- Return `some #[alt_1, ..., alt_n]` if `alt` has multiple LHSs. -/
private def expandMultiAlt? (alt : Syntax) : Option (Array Syntax) := Id.run do
  if isMultiAlt alt then
    some <| alt[0].getArgs.map fun lhs => alt.setArg 0 (mkNullNode #[lhs])
  else
    none

/--
Given `inductionAlts` of the form
```
syntax inductionAlts := "with " (tactic)? withPosition( (colGe inductionAlt)+)
```
Return `some inductionAlts'` if one of the alternatives have multiple LHSs, in the new `inductionAlts'`
all alternatives have a single LHS.

Remark: the `RHS` of alternatives with multi LHSs is copied.
-/
private def expandInductionAlts? (inductionAlts : Syntax) : Option Syntax := Id.run do
  let alts := getAltsOfInductionAlts inductionAlts
  if alts.any isMultiAlt then
    let mut altsNew := #[]
    for alt in alts do
      if let some alt' := expandMultiAlt? alt then
        altsNew := altsNew ++ alt'
      else
        altsNew := altsNew.push alt
    some <| inductionAlts.setArg 2 (mkNullNode altsNew)
  else
    none

/--
Expand
```
syntax "induction " term,+ (" using " ident)?  ("generalizing " (colGt term:max)+)? (inductionAlts)? : tactic
```
if `inductionAlts` has an alternative with multiple LHSs.
-/
private def expandInduction? (induction : Syntax) : Option Syntax := do
  let optInductionAlts := induction[4]
  guard <| !optInductionAlts.isNone
  let inductionAlts' ← expandInductionAlts? optInductionAlts[0]
  return induction.setArg 4 (mkNullNode #[inductionAlts'])

/--
Expand
```
syntax "cases " casesTarget,+ (" using " ident)? (inductionAlts)? : tactic
```
if `inductionAlts` has an alternative with multiple LHSs.
-/
private def expandCases? (induction : Syntax) : Option Syntax := do
  let optInductionAlts := induction[3]
  guard <| !optInductionAlts.isNone
  let inductionAlts' ← expandInductionAlts? optInductionAlts[0]
  return induction.setArg 3 (mkNullNode #[inductionAlts'])

/--
  We may have at most one `| _ => ...` (wildcard alternative), and it must not set variable names.
  The idea is to make sure users do not write unstructured tactics. -/
private def checkAltsOfOptInductionAlts (optInductionAlts : Syntax) : TacticM Unit :=
  unless optInductionAlts.isNone do
    let mut found := false
    for alt in getAltsOfInductionAlts optInductionAlts[0] do
      let n := getAltName alt
      if n == `_ then
        unless (getAltVars alt).isEmpty do
          throwErrorAt alt "wildcard alternative must not specify variable names"
        if found then
          throwErrorAt alt "more than one wildcard alternative '| _ => ...' used"
        found := true

def getInductiveValFromMajor (major : Expr) : TacticM InductiveVal :=
  liftMetaMAtMain fun mvarId => do
    let majorType ← inferType major
    let majorType ← whnf majorType
    matchConstInduct majorType.getAppFn
      (fun _ => Meta.throwTacticEx `induction mvarId m!"major premise type is not an inductive type {indentExpr majorType}")
      (fun val _ => pure val)

/--
Elaborates the term in the `using` clause. We want to allow parameters to be instantiated
(e.g. `using foo (p := …)`), but preserve other parameters, like the motives, as parameters,
without turning them into MVars. So this uses `abstractMVars` at the end. This is inspired by
`Lean.Elab.Tactic.addSimpTheorem`.

It also elaborates without `heedElabAsElim` so that users can use constants that are marked
`elabAsElim` in the `using` clause`.
-/
private def elabTermForElim (stx : Syntax) : TermElabM Expr := do
  -- Short-circuit elaborating plain identifiers
  if stx.isIdent then
    if let some e ← Term.resolveId? stx (withInfo := true) then
      return e
  Term.withoutErrToSorry <| Term.withoutHeedElabAsElim do
    let e ← Term.elabTerm stx none (implicitLambda := false)
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars (levels := false) e
      return r.expr
    else
      return e

register_builtin_option tactic.customEliminators : Bool := {
  defValue := true
  group    := "tactic"
  descr    := "enable using custom eliminators in the 'induction' and 'cases' tactics \
    defined using the '@[induction_eliminator]' and '@[cases_eliminator]' attributes"
}

-- `optElimId` is of the form `("using" term)?`
private def getElimNameInfo (optElimId : Syntax) (targets : Array Expr) (induction : Bool) : TacticM ElimInfo := do
  if optElimId.isNone then
    if tactic.customEliminators.get (← getOptions) then
      if let some elimName ← getCustomEliminator? targets induction then
        return ← getElimInfo elimName
    unless targets.size == 1 do
      throwError "eliminator must be provided when multiple targets are used (use 'using <eliminator-name>'), and no default eliminator has been registered using attribute `[eliminator]`"
    let indVal ← getInductiveValFromMajor targets[0]!
    if induction && indVal.all.length != 1 then
      throwError "'induction' tactic does not support mutually inductive types, the eliminator '{mkRecName indVal.name}' has multiple motives"
    if induction && indVal.isNested then
      throwError "'induction' tactic does not support nested inductive types, the eliminator '{mkRecName indVal.name}' has multiple motives"
    let elimName := if induction then mkRecName indVal.name else mkCasesOnName indVal.name
    getElimInfo elimName indVal.name
  else
    let elimTerm := optElimId[1]
    let elimExpr ← withRef elimTerm do elabTermForElim elimTerm
    -- not a precise check, but covers the common cases of T.recOn / T.casesOn
    -- as well as user defined T.myInductionOn to locate the constructors of T
    let baseName? ← do
      let some elimName := elimExpr.getAppFn.constName? | pure none
      if ← isInductive elimName.getPrefix then
        pure (some elimName.getPrefix)
      else
        pure none
    withRef elimTerm <| getElimExprInfo elimExpr baseName?

private def shouldGeneralizeTarget (e : Expr) : MetaM Bool := do
  if let .fvar fvarId .. := e then
    return (←  fvarId.getDecl).hasValue -- must generalize let-decls
  else
    return true

private def generalizeTargets (exprs : Array Expr) : TacticM (Array Expr) := do
  if (← withMainContext <| exprs.anyM (shouldGeneralizeTarget ·)) then
    liftMetaTacticAux fun mvarId => do
      let (fvarIds, mvarId) ← mvarId.generalize (exprs.map fun expr => { expr })
      return (fvarIds.map mkFVar, [mvarId])
  else
    return exprs

@[builtin_tactic Lean.Parser.Tactic.induction, builtin_incremental]
def evalInduction : Tactic := fun stx =>
  match expandInduction? stx with
  | some stxNew => withMacroExpansion stx stxNew <| evalTactic stxNew
  | _ => focus do
    let targets ← withMainContext <| stx[1].getSepArgs.mapM (elabTerm · none)
    let targets ← generalizeTargets targets
    let elimInfo ← withMainContext <| getElimNameInfo stx[2] targets (induction := true)
    let mvarId ← getMainGoal
    -- save initial info before main goal is reassigned
    let initInfo ← mkTacticInfo (← getMCtx) (← getUnsolvedGoals) (← getRef)
    let tag ← mvarId.getTag
    mvarId.withContext do
      let targets ← addImplicitTargets elimInfo targets
      checkTargets targets
      let targetFVarIds := targets.map (·.fvarId!)
      let (n, mvarId) ← generalizeVars mvarId stx targets
      mvarId.withContext do
        let result ← withRef stx[1] do -- use target position as reference
          ElimApp.mkElimApp elimInfo targets tag
        trace[Elab.induction] "elimApp: {result.elimApp}"
        ElimApp.setMotiveArg mvarId result.motive targetFVarIds
        -- drill down into old and new syntax: allow reuse of an rhs only if everything before it is
        -- unchanged
        -- everything up to the alternatives must be unchanged for reuse
        Term.withNarrowedArgTacticReuse (stx := stx) (argIdx := 4) fun optInductionAlts => do
        withAltsOfOptInductionAlts optInductionAlts fun alts => do
          let optPreTac := getOptPreTacOfOptInductionAlts optInductionAlts
          mvarId.assign result.elimApp
          ElimApp.evalAlts elimInfo result.alts optPreTac alts initInfo (numGeneralized := n) (toClear := targetFVarIds)
          appendGoals result.others.toList
where
  checkTargets (targets : Array Expr) : MetaM Unit := do
    let mut foundFVars : FVarIdSet := {}
    for target in targets do
      unless target.isFVar do
        throwError "index in target's type is not a variable (consider using the `cases` tactic instead){indentExpr target}"
      if foundFVars.contains target.fvarId! then
        throwError "target (or one of its indices) occurs more than once{indentExpr target}"
      foundFVars := foundFVars.insert target.fvarId!

def elabCasesTargets (targets : Array Syntax) : TacticM (Array Expr × Array (Ident × FVarId)) :=
  withMainContext do
    let mut hIdents := #[]
    let mut args := #[]
    for target in targets do
      let hName? ← if target[0].isNone then
        pure none
      else
        hIdents := hIdents.push ⟨target[0][0]⟩
        pure (some target[0][0].getId)
      let expr ← elabTerm target[1] none
      args := args.push { expr, hName? : GeneralizeArg }
    if (← withMainContext <| args.anyM fun arg => shouldGeneralizeTarget arg.expr <||> pure arg.hName?.isSome) then
      liftMetaTacticAux fun mvarId => do
        let argsToGeneralize ← args.filterM fun arg => shouldGeneralizeTarget arg.expr <||> pure arg.hName?.isSome
        let (fvarIdsNew, mvarId) ← mvarId.generalize argsToGeneralize
        -- note: fvarIdsNew contains the `x` variables from `args` followed by all the `h` variables
        let mut result := #[]
        let mut j := 0
        for arg in args do
          if (← shouldGeneralizeTarget arg.expr) || arg.hName?.isSome then
            result := result.push (mkFVar fvarIdsNew[j]!)
            j := j+1
          else
            result := result.push arg.expr
        -- note: `fvarIdsNew[j:]` contains all the `h` variables
        assert! hIdents.size + j == fvarIdsNew.size
        return ((result, hIdents.zip fvarIdsNew[j:]), [mvarId])
    else
      return (args.map (·.expr), #[])

@[builtin_tactic Lean.Parser.Tactic.cases, builtin_incremental]
def evalCases : Tactic := fun stx =>
  match expandCases? stx with
  | some stxNew => withMacroExpansion stx stxNew <| evalTactic stxNew
  | _ => focus do
    -- leading_parser nonReservedSymbol "cases " >> sepBy1 (group majorPremise) ", " >> usingRec >> optInductionAlts
    let (targets, toTag) ← elabCasesTargets stx[1].getSepArgs
    let targetRef := stx[1]
    let elimInfo ← withMainContext <| getElimNameInfo stx[2] targets (induction := false)
    let mvarId ← getMainGoal
    -- save initial info before main goal is reassigned
    let initInfo ← mkTacticInfo (← getMCtx) (← getUnsolvedGoals) (← getRef)
    let tag ← mvarId.getTag
    mvarId.withContext do
      let targets ← addImplicitTargets elimInfo targets
      let result ← withRef targetRef <| ElimApp.mkElimApp elimInfo targets tag
      let elimArgs := result.elimApp.getAppArgs
      let targets ← elimInfo.targetsPos.mapM fun i => instantiateMVars elimArgs[i]!
      let motiveType ← inferType elimArgs[elimInfo.motivePos]!
      let mvarId ← generalizeTargetsEq mvarId motiveType targets
      let (targetsNew, mvarId) ← mvarId.introN targets.size
      mvarId.withContext do
        ElimApp.setMotiveArg mvarId elimArgs[elimInfo.motivePos]!.mvarId! targetsNew
        mvarId.assign result.elimApp
        -- drill down into old and new syntax: allow reuse of an rhs only if everything before it is
        -- unchanged
        -- everything up to the alternatives must be unchanged for reuse
        Term.withNarrowedArgTacticReuse (stx := stx) (argIdx := 3) fun optInductionAlts => do
        withAltsOfOptInductionAlts optInductionAlts fun alts => do
          let optPreTac := getOptPreTacOfOptInductionAlts optInductionAlts
          ElimApp.evalAlts elimInfo result.alts optPreTac alts initInfo
            (numEqs := targets.size) (toClear := targetsNew) (toTag := toTag)

builtin_initialize
  registerTraceClass `Elab.cases
  registerTraceClass `Elab.induction

end Lean.Elab.Tactic
