/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Util.CollectFVars
public import Lean.AuxRecursor
public import Lean.Parser.Term
public import Lean.Meta.RecursorInfo
public import Lean.Meta.CollectMVars
public import Lean.Meta.Tactic.ElimInfo
public import Lean.Meta.Tactic.FunIndInfo
public import Lean.Meta.Tactic.Induction
public import Lean.Meta.Tactic.Cases
public import Lean.Meta.Tactic.FunIndCollect
public import Lean.Meta.GeneralizeVars
public import Lean.Elab.App
public import Lean.Elab.Match
public import Lean.Elab.Tactic.ElabTerm
public import Lean.Elab.Tactic.Generalize

public section

namespace Lean.Elab.Tactic
open Meta

/-
  Given an `inductionAlt` of the form
  ```
  syntax inductionAltLHS := "| " (group("@"? ident) <|> hole) (ident <|> hole)*
  syntax inductionAlt  := ppDedent(ppLine) inductionAltLHS+ (" => " (hole <|> syntheticHole <|> tacticSeq))?
  ```
  We assume that the syntax has been expanded. There is exactly one `inductionAltLHS`,
  and `" => " (hole <|> syntheticHole <|> tacticSeq)` is present
-/
private def getAltLhses (alt : Syntax) : Syntax :=
  alt[0]
private def getFirstAltLhs (alt : Syntax) : Syntax :=
  (getAltLhses alt)[0]
/-- Return `inductionAlt` name. It assumes `alt` does not have multiple `inductionAltLHS`. Returns `none` if the name is missing. -/
private def getAltName? (alt : Syntax) : Option Name :=
  let head := (getFirstAltLhs alt)[1]
  if head.isOfKind ``Parser.Term.hole then
    if head[0].isMissing then none else some `_
  else
    let ident := head[1]
    if ident.isOfKind identKind then some ident.getId.eraseMacroScopes else none
/-- Returns true if the the alternative is for a wildcard, and that the wildcard is not due to a syntax error. -/
private def isAltWildcard (altStx : Syntax) : Bool :=
  getAltName? altStx == some `_
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
private def hasAltRHS (alt : Syntax) : Bool :=
  alt[1].getNumArgs > 0
private def getAltRHS (alt : Syntax) : Syntax :=
  alt[1][1]
private def getAltDArrow (alt : Syntax) : Syntax :=
  alt[1][0]

-- Return true if `stx` is a term occurring in the RHS of the induction/cases tactic
def isHoleRHS (rhs : Syntax) : Bool :=
  rhs.isOfKind ``Parser.Term.syntheticHole || rhs.isOfKind ``Parser.Term.hole

def evalAlt (mvarId : MVarId) (alt : Syntax) (addInfo : TermElabM Unit) : TacticM Unit := do
  if !hasAltRHS alt then
    throwErrorAt alt "(internal error) RHS was not expanded"
  else
    let rhs := getAltRHS alt
    withCaseRef (getAltDArrow alt) rhs do
      let goals ← getGoals
      try
        setGoals [mvarId]
        let withInfo (m : TacticM Unit) :=
          withTacticInfoContext (mkNullNode #[getAltLhses alt, getAltDArrow alt]) do
            addInfo; m
        if isHoleRHS rhs then
          withInfo <| mvarId.withContext do
            let mvarDecl ← mvarId.getDecl
            -- Elaborate ensuring that `_` is interpreted as `?_`.
            let (val, gs') ← elabTermWithHoles rhs mvarDecl.type `induction (parentTag? := mvarDecl.userName) (allowNaturalHoles := true)
            mvarId.assign val
            setGoals gs'
        else
          -- Admit remaining goals outside the TacticInfo so that the infoview
          -- won't report "no goals" in incomplete proofs.
          closeUsingOrAdmit <| withInfo <| evalTactic rhs
      finally
        pushGoals goals

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
  elimApp     : Expr
  elimArgs    : Array Expr
  motive      : MVarId
  alts        : Array Alt
  others      : Array MVarId
  complexArgs : Array Expr

/--
  Construct the an eliminator/recursor application. `targets` contains the explicit and implicit
  targets for the eliminator, not yet generalized.
  For example, the indices of builtin recursors are considered implicit targets.
  Remark: the method `addImplicitTargets` may be used to compute the sequence of implicit and
  explicit targets from the explicit ones.
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
          throwError "Insufficient number of targets for `{elimInfo.elimExpr}`"
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
      let s ← get
      let ctx ← read
      unless s.targetPos = ctx.targets.size do
        throwError "Unexpected number of targets for `{elimInfo.elimExpr}`"
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
      throwError "Internal error in mkElimApp: Motive not found"
  let complexArgs ← s.fType.withApp fun f motiveArgs => do
    unless f == mkMVar motive do
      throwError "Internal error in mkElimApp: Expected application of {motive}:{indentExpr s.fType}"
    -- Sanity-checking that the motive is applied to the targets.
    -- NB: The motive can take them in a different order than the eliminator itself
    for motiveArg in motiveArgs[*...targets.size] do
      unless targets.contains motiveArg do
        throwError "Internal error in mkElimApp: Expected first {targets.size} arguments of motive \
          in conclusion to be one of the targets:{indentExpr s.fType}"
    pure motiveArgs[targets.size...*]
  let elimApp ← instantiateMVars s.f
  -- `elimArgs` is the argument list that the offsets in `elimInfo` work with
  let elimArgs := elimApp.getAppArgs[elimInfo.elimExpr.getAppNumArgs...*]
  return { elimApp, elimArgs, alts, others, motive, complexArgs }

/--
Given a goal `... targets ... |- C[targets, complexArgs]` associated with `mvarId`,
where `complexArgs` are the the complex (i.e. non-target) arguments to the motive in the conclusion
of the eliminator, construct `motiveArg := fun targets rs => C[targets, rs]`

This checks if the type of the complex arguments match what's expected by the motive, and
ignores them otherwise. This limits the ability of `cases` to use unfolding function
principles with dependent types, because after generalization of the targets, the types do
no longer match. This can likely be improved.
-/
def setMotiveArg (mvarId : MVarId) (motiveArg : MVarId) (targets : Array FVarId) (complexArgs : Array Expr := #[]) : MetaM Unit := do
  let type ← inferType (mkMVar mvarId)

  let motiveType ← inferType (mkMVar motiveArg)
  let exptComplexArgTypes ← arrowDomainsN complexArgs.size (← instantiateForall motiveType (targets.map mkFVar))

  let mut absType := type
  for complexArg in complexArgs.reverse, exptComplexArgType in exptComplexArgTypes.reverse do
    trace[Elab.induction] "setMotiveArg: trying to abstract over {complexArg}, expected type {exptComplexArgType}"
    let complexArgType ← inferType complexArg
    if (← isDefEq complexArgType exptComplexArgType) then
      let absType' ← kabstract absType complexArg
      let absType' := .lam (← mkFreshUserName `x) complexArgType absType' .default
      if (← isTypeCorrect absType') then
        absType := absType'
      else
        trace[Elab.induction] "Not abstracting goal over {complexArg}, resulting term is not type correct:{indentExpr absType'} }"
        absType := .lam (← mkFreshUserName `x) complexArgType absType .default
    else
      trace[Elab.induction] "Not abstracting goal over {complexArg}, its type {complexArgType} does not match the expected {exptComplexArgType}"
      absType := .lam (← mkFreshUserName `x) exptComplexArgType absType .default

  let motive ← mkLambdaFVars (targets.map mkFVar) absType
  let motiverInferredType ← inferType motive
  unless (← isDefEqGuarded motiverInferredType motiveType) do
    throwError "Type mismatch when assigning motive{indentExpr motive}\n{← mkHasTypeButIsExpectedMsg motiverInferredType motiveType}"
  motiveArg.assign motive

private def getAltNumFields (elimInfo : ElimInfo) (altName : Name) : TermElabM Nat := do
  for altInfo in elimInfo.altsInfo do
    if altInfo.name == altName then
      return altInfo.numFields
  throwError "Unknown alternative name `{altName}`"

private def checkAltNames (alts : Array Alt) (altsSyntax : Array Syntax) : TacticM Unit := do
  let mut seenNames : Array Name := #[]
  let mut invalidNames : Array (Syntax × Name) := #[]
  for h : i in *...altsSyntax.size do
    let altStx := altsSyntax[i]
    if isAltWildcard altStx && i != altsSyntax.size - 1 then
      withRef altStx <| throwError "Invalid occurrence of the wildcard alternative `| _ => ...`: It must be the last alternative"
    if let some altName := getAltName? altStx then
      if altName != `_ then
        if seenNames.contains altName then
          throwOrLogErrorAt altStx m!"Duplicate alternative name `{altName}`"
        else
          seenNames := seenNames.push altName
          unless alts.any (·.name == altName) do
            invalidNames := invalidNames.push (altStx, altName)
    else
      invalidNames := invalidNames.push (altStx, .anonymous)
  unless invalidNames.isEmpty do
    let unhandledAlts := alts.filter fun alt => !seenNames.contains alt.name
    let unhandledAltsMessages := unhandledAlts.map (m!"`{·.name}`")
    let msg :=
      if unhandledAlts.isEmpty then
        m!"There are no unhandled alternatives"
      else
        m!"Expected {.orList unhandledAltsMessages.toList}"
    for (altStx, altName) in invalidNames do
      if altName.isAnonymous then
        throwOrLogErrorAt altStx m!"Missing alternative name: {msg}"
      else
        throwOrLogErrorAt altStx m!"Invalid alternative name `{altName}`: {msg}"

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
    -- arguments are explicit or implicit can be found in `introNImp`,
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
def evalAlts (elimInfo : ElimInfo) (alts : Array Alt) (optPreTac : Syntax) (altStxs? : Option (Array Syntax))
    (mkInfo : TacticM Info) (tacStx : Syntax)
    (numEqs : Nat := 0) (generalized : Array FVarId := #[]) (toClear : Array FVarId := #[])
    (toTag : Array (Ident × FVarId) := #[]) : TacticM Unit := do
  let hasAlts := altStxs?.isSome
  -- We defer admitting goals for missing alternatives so that they can be captured by `mkInfo`.
  let toAdmit ←
    if hasAlts then
      -- HACK: because this node may have the same span as the original tactic,
      -- we need to take all the info trees we have produced so far and re-nest them
      -- inside this node as well
      let treesSaved ← getResetInfoTrees
      withInfoContext ((modifyInfoState fun s => { s with trees := treesSaved }) *> goWithInfo) mkInfo
    else
      goWithInfo
  toAdmit.forM fun mvarId => admitGoal mvarId
where
  -- continuation in the correct info context
  goWithInfo : TacticM (List MVarId) := do
    if let some altStxs := altStxs? then
      if let some tacSnap := (← readThe Term.Context).tacSnap? then
        -- incrementality: create a new promise for each alternative, resolve current snapshot to
        -- them, eventually put each of them back in `Context.tacSnap?` in `applyAltStx`
        let finished ← IO.Promise.new
        let altPromises ← altStxs.mapM fun _ => IO.Promise.new
        let cancelTk? := (← readThe Core.Context).cancelTk?
        tacSnap.new.resolve {
          -- save all relevant syntax here for comparison with next document version
          stx := mkNullNode altStxs
          diagnostics := .empty
          inner? := none
          finished := { stx? := mkNullNode altStxs, reportingRange := .inherit, task := finished.resultD default, cancelTk? }
          next := Array.zipWith
            (fun stx prom => { stx? := some stx, task := prom.resultD default, cancelTk? })
            altStxs altPromises
        }
        let toAdmit ← goWithIncremental <| altPromises.mapIdx fun i prom => {
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
        finished.resolve {
          diagnostics := .empty
          state? := (← saveState)
          moreSnaps := (← Core.getAndEmptySnapshotTasks)
        }
        return toAdmit

    goWithIncremental #[]

  -- continuation in the correct incrementality context
  goWithIncremental (tacSnaps : Array (SnapshotBundle TacticParsedSnapshot)) : TacticM (List MVarId) := withRef tacStx do
    let hasAlts := altStxs?.isSome
    let altStxs := altStxs?.getD #[]
    let mut alts := alts
    let mut toAdmit := []

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
    for h : altStxIdx in *...altStxs.size do
      let altStx := altStxs[altStxIdx]
      let some altName := getAltName? altStx | continue
      if let some i := alts.findFinIdx? (·.1 == altName) then
        -- cover named alternative
        applyAltStx tacSnaps altStxs altStxIdx altStx alts[i]
        alts := alts.eraseIdx i
      else if isAltWildcard altStx then
        if alts.isEmpty then
          throwOrLogErrorAt altStx m!"Wildcard alternative is not needed"
        else
          -- cover all remaining alternatives
          for alt in alts do
            applyAltStx tacSnaps altStxs altStxIdx altStx alt
          alts := #[]
      else
        -- Skip this alternative. We have already validated the alternatives in `checkAltNames`
        -- and thrown/logged errors.
        pure ()

    -- now process remaining alternatives; these might either be unreachable or we're in `induction`
    -- without `with`. In all other cases, remaining alternatives are flagged as errors.
    for { name := altName, info, mvarId := altMVarId } in alts do
      let numFields ← getAltNumFields elimInfo altName
      let mut (_, altMVarId) ← altMVarId.introN numFields
      let some (altMVarId', subst) ← Cases.unifyEqs? numEqs altMVarId {}
        | continue  -- alternative is not reachable
      altMVarId.withContext do
        for x in subst.domain do
          if let .fvar y := subst.get x then
            if let some decl ← x.findDecl? then
              Elab.pushInfoLeaf (.ofFVarAliasInfo { id := y, baseId := x, userName := decl.userName })
      altMVarId ← if info.provesMotive then
        let (generalized', altMVarId') ← altMVarId'.introNP generalized.size
        altMVarId'.withContext do
          for x in generalized, y in generalized' do
            Elab.pushInfoLeaf (.ofFVarAliasInfo { id := y, baseId := x, userName := ← y.getUserName })
        pure altMVarId'
      else
        pure altMVarId'
      for fvarId in toClear do
        altMVarId ← altMVarId.tryClear fvarId
      altMVarId.withContext do
        for (stx, fvar) in toTag do
          Term.addLocalVarInfo stx (subst.get fvar)
      let some altMVarIds ← applyPreTac altMVarId
        | continue
      appendGoals altMVarIds
      if hasAlts && !altMVarIds.isEmpty then
        throwOrLogErrorAt tacStx m!"Alternative `{altName}` has not been provided"
        toAdmit := altMVarIds ++ toAdmit
    return toAdmit

  /-- Applies syntactic alternative to alternative goal. -/
  applyAltStx tacSnaps altStxs altStxIdx altStx alt := withRef altStx do
    let { name := altName, info, mvarId := altMVarId } := alt
    -- also checks for unknown alternatives
    let numFields ← getAltNumFields elimInfo altName
    let altVars := getAltVars altStx
    let numFieldsToName ← if altHasExplicitModifier altStx then pure numFields else getNumExplicitFields altMVarId numFields
    if altVars.size > numFieldsToName then
      throwOrLogError m!"Too many variable names provided at alternative `{altName}`: {altVars.size} provided, but {numFieldsToName} expected"
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
      if !isAltWildcard altStx then
        throwOrLogError m!"Alternative `{altName}` is not needed"
    let some (altMVarId', subst) ← Cases.unifyEqs? numEqs altMVarId {}
      | unusedAlt
    altMVarId.withContext do
      for x in subst.domain do
        if let .fvar y := subst.get x then
          if let some decl ← x.findDecl? then
            Elab.pushInfoLeaf (.ofFVarAliasInfo { id := y, baseId := x, userName := decl.userName })
    altMVarId ← if info.provesMotive then
      let (generalized', altMVarId') ← altMVarId'.introNP generalized.size
      altMVarId'.withContext do
        for x in generalized, y in generalized' do
          Elab.pushInfoLeaf (.ofFVarAliasInfo { id := y, baseId := x, userName := ← y.getUserName })
      pure altMVarId'
    else
      pure altMVarId'
    for fvarId in toClear do
      altMVarId ← altMVarId.tryClear fvarId
    altMVarId.withContext do
      for (stx, fvar) in toTag do
        Term.addLocalVarInfo stx (subst.get fvar)
    let some altMVarIds ← applyPreTac altMVarId
      | return
    if altMVarIds.isEmpty then
      return (← unusedAlt)

    -- select corresponding snapshot bundle for incrementality of this alternative
    -- note that `tacSnaps[altStxIdx]?` is `none` if `tacSnap?` was `none` to begin with
    withTheReader Term.Context ({ · with tacSnap? := tacSnaps[altStxIdx]? }) do
    -- all previous alternatives have to be unchanged for reuse
    Term.withNarrowedArgTacticReuse (stx := mkNullNode altStxs) (argIdx := altStxIdx) fun altStx => do
    -- everything up to rhs has to be unchanged for reuse
    Term.withNarrowedArgTacticReuse (stx := altStx) (argIdx := 1) fun rhs? => do
    Term.withNarrowedArgTacticReuse (stx := rhs?) (argIdx := 1) fun _rhs => do
    -- disable reuse if rhs is run multiple times
    Term.withoutTacticIncrementality (altMVarIds.length != 1 || isAltWildcard altStx) do
      for altMVarId' in altMVarIds do
        evalAlt altMVarId' altStx addInfo

  /-- Applies `induction .. with $preTac | ..`, if any, to an alternative goal. -/
  applyPreTac (mvarId : MVarId) : TacticM (Option (List MVarId)) :=
    if optPreTac.isNone then
      return some [mvarId]
    else
      -- disable incrementality for the pre-tactic to avoid non-monotonic progress reporting; it
      -- would be possible to include a custom task around the pre-tac with an appropriate range in
      -- the snapshot such that it is cached as well if it turns out that this is valuable
      Term.withoutTacticIncrementality true do
        let go := evalTacticAt optPreTac[0] mvarId
        if (← read).recover then
          let saved ← saveState
          Tactic.tryCatch go fun ex => do
            logException ex
            let msgLog ← Core.getMessageLog
            saved.restore (restoreInfo := false)
            Core.setMessageLog msgLog
            admitGoal mvarId
            return none
        else
          go

end ElimApp

/-
  Recall that
  ```
  generalizingVars := optional (" generalizing " >> many1 ident)
  «induction»  := leading_parser nonReservedSymbol "induction " >> majorPremise >> usingRec >> generalizingVars >> optional inductionAlts
  ```
  `stx` is syntax for `induction` or `fun_induction`. -/
private def getUserGeneralizingFVarIds (stx : Syntax) : TacticM (Array FVarId) :=
  withRef stx do
    let generalizingStx :=
    if stx.getKind == ``Lean.Parser.Tactic.induction then
      stx[3]
    else if stx.getKind == ``Lean.Parser.Tactic.funInduction then
      stx[2]
    else
      panic! "getUserGeneralizingFVarIds: Unexpected syntax kind {stx.getKind}"
    if generalizingStx.isNone then
      pure #[]
    else
      trace[Elab.induction] "{generalizingStx}"
      let vars := generalizingStx[1].getArgs
      getFVarIds vars

-- process `generalizingVars` subterm of induction Syntax `stx`.
private def generalizeVars (mvarId : MVarId) (stx : Syntax) (targets : Array Expr) : TacticM (Array FVarId × MVarId) :=
  mvarId.withContext do
    let userFVarIds ← getUserGeneralizingFVarIds stx
    let forbidden ← mkGeneralizationForbiddenSet targets
    let mut s ← getFVarSetToGeneralize targets forbidden
    for userFVarId in userFVarIds do
      if forbidden.contains userFVarId then
        throwError "Variable `{mkFVar userFVarId}` cannot be generalized because the induction target depends on it"
      if s.contains userFVarId then
        throwOrLogError m!"Unnecessary `generalizing` argument: Variable `{mkFVar userFVarId}` is generalized automatically"
      s := s.insert userFVarId
    let fvarIds ← sortFVarIds s.toArray
    let (fvarIds, mvarId') ← mvarId.revert fvarIds
    return (fvarIds, mvarId')

/--
Given `inductionAlts` of the form
```
syntax inductionAlts := "with " (tactic)? withPosition( (colGe inductionAlt)*)
```
Return an array containing its alternatives.
-/
private def getAltsOfInductionAlts (inductionAlts : Syntax) : Array Syntax :=
  inductionAlts[2].getArgs

/--
Given `inductionAlts` of the form
```
syntax inductionAlts := "with " (tactic)? withPosition( (colGe inductionAlt)*)
```
runs `cont (some alts)` where `alts` is an array containing all `inductionAlt`s while disabling incremental
reuse if any other syntax changed. If there's no `with` clause, then runs `cont none`.
-/
private def withAltsOfOptInductionAlts (optInductionAlts : Syntax)
    (cont : Option (Array Syntax) → TacticM α) : TacticM α :=
  Term.withNarrowedTacticReuse (stx := optInductionAlts) (fun optInductionAlts =>
    if optInductionAlts.isNone then
      -- if there are no alternatives, what to compare is irrelevant as there will be no reuse
      (mkNullNode #[], mkNullNode #[])
    else
      -- if there are no alts, then use the `with` token for `inner` for a ref for messages
      let altStxs := optInductionAlts[0].getArg 2
      let inner := if altStxs.getNumArgs > 0 then altStxs else optInductionAlts[0][0]
      -- `with` and tactic applied to all branches must be unchanged for reuse
      (mkNullNode optInductionAlts[0].getArgs[*...2], inner))
    (fun alts? =>
      if optInductionAlts.isNone then      -- no `with` clause
        cont none
      else if alts?.isOfKind nullKind then -- has alts
        cont (some alts?.getArgs)
      else                                 -- has `with` clause, but no alts
        cont (some #[]))

private def getOptPreTacOfOptInductionAlts (optInductionAlts : Syntax) : Syntax :=
  if optInductionAlts.isNone then mkNullNode else optInductionAlts[0][1]

/--
Returns true if the `Lean.Parser.Tactic.inductionAlt` either has more than one alternative
or has no RHS.
-/
private def shouldExpandAlt (alt : Syntax) : Bool :=
  alt[0].getNumArgs > 1 || (1 < alt.getNumArgs && alt[1].getNumArgs == 0)

/--
Returns `some #[alt_1, ..., alt_n]` if `alt` has multiple LHSs or if `alt` has no RHS.
If there is no RHS, it is filled in with a hole.
-/
private def expandAlt? (alt : Syntax) : Option (Array Syntax) := Id.run do
  if shouldExpandAlt alt then
    some <| alt[0].getArgs.map fun lhs =>
      let alt := alt.setArg 0 (mkNullNode #[lhs])
      if 1 < alt.getNumArgs && alt[1].getNumArgs == 0 then
        alt.setArg 1 <| mkNullNode #[mkAtomFrom lhs "=>", mkHole lhs]
      else
        alt
  else
    none

/--
Given `inductionAlts` of the form
```
syntax inductionAlts := "with " (tactic)? withPosition( (colGe inductionAlt)*)
```
Return `some inductionAlts'` if one of the alternatives has multiple LHSs or no RHS.
In the new `inductionAlts'` all alternatives have a single LHS.

Remark: the `RHS` of alternatives with multi LHSs is copied.
-/
private def expandInductionAlts? (inductionAlts : Syntax) : Option Syntax := Id.run do
  let alts := getAltsOfInductionAlts inductionAlts
  if alts.any shouldExpandAlt then
    let mut altsNew := #[]
    for alt in alts do
      if let some alt' := expandAlt? alt then
        altsNew := altsNew ++ alt'
      else
        altsNew := altsNew.push alt
    some <| inductionAlts.setArg 2 (mkNullNode altsNew)
  else
    none

private def inductionAltsPos (stx : Syntax) : Nat :=
  if stx.getKind == ``Lean.Parser.Tactic.induction then
    4
  else if stx.getKind == ``Lean.Parser.Tactic.cases then
    3
  else if stx.getKind == ``Lean.Parser.Tactic.funInduction then
    3
  else if stx.getKind == ``Lean.Parser.Tactic.funCases then
    2
  else
    panic! s!"inductionAltsSyntaxPos: Unexpected syntax kind {stx.getKind}"

/--
Expand
```
syntax "induction " term,+ (" using " ident)?  ("generalizing " (colGt term:max)+)? (inductionAlts)? : tactic
```
if `inductionAlts` has an alternative with multiple LHSs, and likewise for
`cases`, `fun_induction`, `fun_cases`.
-/
private def expandInduction? (induction : Syntax) : Option Syntax := do
  let inductionAltsPos := inductionAltsPos induction
  let optInductionAlts := induction[inductionAltsPos]
  guard <| !optInductionAlts.isNone
  let inductionAlts' ← expandInductionAlts? optInductionAlts[0]
  return induction.setArg inductionAltsPos (mkNullNode #[inductionAlts'])

/--
  We may have at most one `| _ => ...` (wildcard alternative), and it must not set variable names.
  The idea is to make sure users do not write unstructured tactics. -/
private def checkAltsOfOptInductionAlts (optInductionAlts : Syntax) : TacticM Unit :=
  unless optInductionAlts.isNone do
    let mut found := false
    for alt in getAltsOfInductionAlts optInductionAlts[0] do
      if isAltWildcard alt then
        unless (getAltVars alt).isEmpty do
          throwErrorAt alt "The wildcard alternative `| _ => ...` must not specify variable names"
        if found then
          throwErrorAt alt "More than one wildcard alternative `| _ => ...` used"
        found := true

def getInductiveValFromMajor (induction : Bool) (major : Expr) : TacticM InductiveVal :=
  liftMetaMAtMain fun mvarId => do
    let majorType ← inferType major
    let majorType ← whnf majorType
    matchConstInduct majorType.getAppFn
      (fun _ => do
        let tacticName := if induction then `induction else `cases
        let mut hint := m!"\n\nExplanation: the `{tacticName}` tactic is for constructor-based reasoning \
          as well as for applying custom {tacticName} principles with a 'using' clause or a registered '@[{tacticName}_eliminator]' theorem. \
          The above type neither is an inductive type nor has a registered theorem."
        if majorType.isProp then
          hint := m!"{hint}\n\n\
            Consider using the 'by_cases' tactic, which does true/false reasoning for propositions."
        else if majorType.isType then
          hint := m!"{hint}\n\n\
            Type universes are not inductive types, and type-constructor-based reasoning is not possible. \
            This is a strong limitation. According to Lean's underlying theory, the only provable distinguishing \
            feature of types is their cardinalities."
        Meta.throwTacticEx tacticName mvarId m!"major premise type is not an inductive type{indentExpr majorType}{hint}")
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
  let getBaseName? (elimName : Name) : MetaM (Option Name) := do
    -- not a precise check, but covers the common cases of T.recOn / T.casesOn
    -- as well as user defined T.myInductionOn to locate the constructors of T
    let t := elimName.getPrefix
    if ← isInductive t then
      return some t
    else
      return none
  if optElimId.isNone then
    if tactic.customEliminators.get (← getOptions) then
      if let some elimName ← getCustomEliminator? targets induction then
        return ← getElimInfo elimName (← getBaseName? elimName)
    unless targets.size == 1 do
      throwMissingEliminator
    let indVal ← getInductiveValFromMajor induction targets[0]!
    if induction && indVal.all.length != 1 then
      throwUnsupportedInductionType indVal.name "mutually inductive"
    if induction && indVal.isNested then
      throwUnsupportedInductionType indVal.name "a nested inductive type"
    let elimName := if induction then mkRecName indVal.name else mkCasesOnName indVal.name
    getElimInfo elimName indVal.name
  else
    let elimTerm := optElimId[1]
    let elimExpr ← withRef elimTerm do elabTermForElim elimTerm
    let baseName? ← do
      let some elimName := elimExpr.getAppFn.constName? | pure none
      getBaseName? elimName
    withRef elimTerm <| getElimExprInfo elimExpr baseName?
where
  throwMissingEliminator :=
    let tacName := if induction then "induction" else "cases"
    throwError m!"Missing eliminator: An eliminator must be provided when multiple induction \
          targets are specified and no default eliminator has been registered"
          ++ .hint' m!"Write `using <eliminator-name>` to specify an eliminator, or register a default \
                        eliminator with the attribute `[{tacName}_eliminator]`"
  throwUnsupportedInductionType (name : Name) (kind : String) :=
    throwError m!"The `induction` tactic does not support the type `{name}` because it is {kind}"
        ++ .hint' "Consider using the `cases` tactic instead"

private def shouldGeneralizeTarget (e : Expr) : MetaM Bool := do
  if let .fvar fvarId .. := e then
    return (← fvarId.getDecl).hasValue -- must generalize let-decls
  else
    return true


/-- View of `Lean.Parser.Tactic.elimTarget`. -/
structure ElimTargetView where
  hIdent? : Option Ident
  term    : Syntax

/-- Interprets a `Lean.Parser.Tactic.elimTarget`. -/
def mkTargetView (target : Syntax) : TacticM ElimTargetView := do
  match target with
  | `(Parser.Tactic.elimTarget| $[$hIdent?:ident :]? $term) =>
    return { hIdent?, term }
  | `(Parser.Tactic.elimTarget| _%$hole : $term) =>
    let hIdent? := some <| mkIdentFrom hole (canonical := true) (← mkFreshBinderNameForTactic `h)
    return { hIdent?, term }
  | _ => return { hIdent? := none, term := .missing }

/-- Elaborated `ElimTargetView`. -/
private structure ElimTargetInfo where
  view : ElimTargetView
  expr : Expr
  arg? : Option GeneralizeArg

/--
Elaborates the targets (`Lean.Parser.Tactic.elimTarget`),
generalizing them if requested or if otherwise necessary.

Returns
1. the targets as fvars and
2. an array of identifier/fvarid pairs so that the `induction`/`cases` tactic can
   annotate any user-supplied target hypothesis names using `Term.addLocalVarInfo`.

Modifies the current goal when generalizing.
-/
def elabElimTargets (targets : Array Syntax) : TacticM (Array Expr × Array (Ident × FVarId)) :=
  withMainContext do
    let infos : Array ElimTargetInfo ← targets.mapM fun target => do
      let view ← mkTargetView target
      let expr ← elabTerm view.term none
      let arg? : Option GeneralizeArg :=
        if let some hIdent := view.hIdent? then
          some { expr, hName? := hIdent.getId }
        else if ← shouldGeneralizeTarget expr then
          some { expr }
        else
          none
      pure { view, expr, arg? }
    if infos.all (·.arg?.isNone) then
      return (infos.map (·.expr), #[])
    else
      liftMetaTacticAux fun mvarId => do
        let (fvarIdsNew, mvarId) ← mvarId.generalize (infos.filterMap (·.arg?))
        -- note: `fvarIdsNew` contains the generalized variables followed by all the `h` variables
        let mut result := #[]
        let mut j := 0
        for info in infos do
          if info.arg?.isSome then
            result := result.push (mkFVar fvarIdsNew[j]!)
            j := j + 1
          else
            result := result.push info.expr
        -- note: `fvarIdsNew[j...*]` contains all the `h` variables
        let hIdents := infos.filterMap (·.view.hIdent?)
        assert! hIdents.size + j == fvarIdsNew.size
        return ((result, hIdents.zip fvarIdsNew[j...*]), [mvarId])

/--
Generalize targets in `fun_induction` and `fun_cases`. Should behave like `elabCasesTargets` with
no targets annotated with `h : _`.
-/
private def generalizeTargets (exprs : Array Expr) : TacticM (Array Expr) := do
  withMainContext do
    let exprToGeneralize ← exprs.filterM (shouldGeneralizeTarget ·)
    if exprToGeneralize.isEmpty then
      return exprs
    liftMetaTacticAux fun mvarId => do
      let (fvarIdsNew, mvarId) ← mvarId.generalize (exprToGeneralize.map ({ expr := · }))
      assert! fvarIdsNew.size == exprToGeneralize.size
      let mut result := #[]
      let mut j := 0
      for expr in exprs do
        if (← shouldGeneralizeTarget expr) then
          result := result.push (mkFVar fvarIdsNew[j]!)
          j := j+1
        else
          result := result.push expr
      return (result, [mvarId])

def checkInductionTargets (targets : Array Expr) : MetaM Unit := do
  let mut foundFVars : FVarIdSet := {}
  for target in targets do
    unless target.isFVar do
      throwError "Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead){indentExpr target}"
    if foundFVars.contains target.fvarId! then
      throwError "Invalid target: Target (or one of its indices) occurs more than once{indentExpr target}"
    foundFVars := foundFVars.insert target.fvarId!

/--
If `stx` has a `with` clause, runs `m` within a tactic info node on `induction/cases ... with`.
The action `m` returns a list of metavariables to admit. The purpose of this is to let the remaining after goals be recorded
in the tactic info, while preserving the semantics that when there is a `with` clause, all unhandled alternatives are admitted.
-/
def mkInitialTacticInfoForInduction (stx : Syntax) : TacticM (TacticM Info) := do
  let altsPos := inductionAltsPos stx
  let range := mkNullNode <| stx.getArgs.extract 0 altsPos |>.push stx[altsPos][0][0]
  mkInitialTacticInfo range

/--
The code path shared between `induction` and `fun_induct`; when we already have an `elimInfo`
and the `targets` contains the implicit targets
-/
private def evalInductionCore (stx : Syntax) (elimInfo : ElimInfo) (targets : Array Expr)
    (toTag : Array (Ident × FVarId) := #[]) : TacticM Unit := do
  let mvarId ← getMainGoal
  -- save initial info before main goal is reassigned
  let mkInitInfo ← mkInitialTacticInfoForInduction stx
  let tag ← mvarId.getTag
  mvarId.withContext do
    checkInductionTargets targets
    let targetFVarIds := targets.map (·.fvarId!)
    let (generalized, mvarId) ← generalizeVars mvarId stx targets
    mvarId.withContext do
      let result ← withRef stx[1] do -- use target position as reference
        ElimApp.mkElimApp elimInfo targets tag
      trace[Elab.induction] "elimApp: {result.elimApp}"
      ElimApp.setMotiveArg mvarId result.motive targetFVarIds result.complexArgs
      -- drill down into old and new syntax: allow reuse of an rhs only if everything before it is
      -- unchanged
      -- everything up to the alternatives must be unchanged for reuse
      Term.withNarrowedArgTacticReuse (stx := stx) (argIdx := inductionAltsPos stx) fun optInductionAlts => do
      withAltsOfOptInductionAlts optInductionAlts fun alts? => do
        let optPreTac := getOptPreTacOfOptInductionAlts optInductionAlts
        mvarId.assign result.elimApp
        ElimApp.evalAlts elimInfo result.alts optPreTac alts? mkInitInfo stx[0]
          (generalized := generalized) (toClear := targetFVarIds) (toTag := toTag)
        appendGoals result.others.toList

@[builtin_tactic Lean.Parser.Tactic.induction, builtin_incremental]
def evalInduction : Tactic := fun stx =>
  match expandInduction? stx with
  | some stxNew => withMacroExpansion stx stxNew <| evalTactic stxNew
  | _ => focus do
    let (targets, toTag) ← elabElimTargets stx[1].getSepArgs
    let elimInfo ← withMainContext <| getElimNameInfo stx[2] targets (induction := true)
    let targets ← withMainContext <| addImplicitTargets elimInfo targets
    evalInductionCore stx elimInfo targets toTag


register_builtin_option tactic.fun_induction.unfolding : Bool := {
  defValue := true
  group    := "tactic"
  descr    := "if set to 'true', then 'fun_induction' and 'fun_cases' will use the “unfolding \
    functional induction (resp. cases) principle” ('….induct_unfolding'/'….fun_cases_unfolding'), \
    which will attempt to replace the function goal of interest in the goal with the appropriate \
    right-hand-side in each case. If 'false', the regular “functional induction principle” \
    ('….induct'/'….fun_cases') is used."
}

/--
Elaborates the `foo args` of `fun_induction` or `fun_cases`, inferring the args if omitted from the goal
-/
def elabFunTargetCall (cases : Bool) (stx : Syntax) : TacticM Expr := do
  match stx with
  | `($id:ident) =>
    let fnName ← realizeGlobalConstNoOverload id
    let unfolding := tactic.fun_induction.unfolding.get (← getOptions)
    let some funIndInfo ← getFunIndInfo? (cases := cases) (unfolding := unfolding) fnName |
      let theoremKind := if cases then "cases" else "induction"
      throwError "No functional {theoremKind} theorem for `{.ofConstName fnName}`, or function is mutually recursive "
    let candidates ← FunInd.collect funIndInfo (← getMainGoal)
    if candidates.isEmpty then
      throwError "Could not find suitable call of `{.ofConstName fnName}` in the goal"
    if candidates.size > 1 then
      throwError "Found more than one suitable call of `{.ofConstName fnName}` in the goal. \
        Please include the desired arguments."
    pure candidates[0]!
  | _ =>
    elabTerm stx none

/--
Elaborates the `foo args` of `fun_induction` or `fun_cases`, returning the `ElabInfo` and targets.
-/
private def elabFunTarget (cases : Bool) (stx : Syntax) : TacticM (ElimInfo × Array Expr) := do
  withRef stx <| withMainContext do
    let funCall ← elabFunTargetCall cases stx
    funCall.withApp fun fn funArgs => do
    let .const fnName fnUs := fn |
      throwError "Expected application headed by a function constant"
    let unfolding := tactic.fun_induction.unfolding.get (← getOptions)
    let some funIndInfo ← getFunIndInfo? (cases := cases) (unfolding := unfolding) fnName |
      let theoremKind := if cases then "cases" else "induction"
      throwError "No functional {theoremKind} theorem for `{.ofConstName fnName}`, or function is mutually recursive "
    if funArgs.size != funIndInfo.params.size then
      throwError "Expected fully applied application of `{.ofConstName fnName}` with \
        {funIndInfo.params.size} arguments, but found {funArgs.size} arguments"
    let mut params := #[]
    let mut targets := #[]
    let mut us := #[]
    for u in fnUs, b in funIndInfo.levelMask do
      if b then
        us := us.push u
    for a in funArgs, kind in funIndInfo.params do
      match kind with
      | .dropped => pure ()
      | .param => params := params.push a
      | .target => targets := targets.push a
    if cases then
      trace[Elab.cases] "us: {us}\nparams: {params}\ntargets: {targets}"
    else
      trace[Elab.induction] "us: {us}\nparams: {params}\ntargets: {targets}"

    let elimExpr := mkAppN (.const funIndInfo.funIndName us.toList) params
    let elimInfo ← getElimExprInfo elimExpr
    unless targets.size = elimInfo.targetsPos.size do
      let tacName := if cases then "fun_cases" else "fun_induction"
      throwError "{tacName} got confused trying to use \
        `{.ofConstName funIndInfo.funIndName}`. Does it take {targets.size} or \
        {elimInfo.targetsPos.size} targets?"
    return (elimInfo, targets)

@[builtin_tactic Lean.Parser.Tactic.funInduction, builtin_incremental]
def evalFunInduction : Tactic := fun stx =>
  match expandInduction? stx with
  | some stxNew => withMacroExpansion stx stxNew <| evalTactic stxNew
  | _ => focus do
    let (elimInfo, targets) ← elabFunTarget (cases := false) stx[1]
    let targets ← generalizeTargets targets
    evalInductionCore stx elimInfo targets

/--
The code path shared between `cases` and `fun_cases`; when we already have an `elimInfo`
and the `targets` contains the implicit targets
-/
def evalCasesCore (stx : Syntax) (elimInfo : ElimInfo) (targets : Array Expr)
    (toTag : Array (Ident × FVarId) := #[]) : TacticM Unit := do
  let targetRef := stx[1]
  let mvarId ← getMainGoal
  -- save initial info before main goal is reassigned
  let mkInitInfo ← mkInitialTacticInfoForInduction stx
  let tag ← mvarId.getTag
  mvarId.withContext do
    let result ← withRef targetRef <| ElimApp.mkElimApp elimInfo targets tag
    let elimArgs := result.elimArgs
    let targets ← elimInfo.targetsPos.mapM fun i => instantiateMVars elimArgs[i]!
    let motiveType ← inferType elimArgs[elimInfo.motivePos]!
    let mvarId ← generalizeTargetsEq mvarId motiveType targets
    let (targetsNew, mvarId) ← mvarId.introN targets.size
    mvarId.withContext do
      ElimApp.setMotiveArg mvarId elimArgs[elimInfo.motivePos]!.mvarId! targetsNew result.complexArgs
      -- drill down into old and new syntax: allow reuse of an rhs only if everything before it is
      -- unchanged
      -- everything up to the alternatives must be unchanged for reuse
      Term.withNarrowedArgTacticReuse (stx := stx) (argIdx := inductionAltsPos stx) fun optInductionAlts => do
      withAltsOfOptInductionAlts optInductionAlts fun alts => do
        let optPreTac := getOptPreTacOfOptInductionAlts optInductionAlts
        mvarId.assign result.elimApp
        ElimApp.evalAlts elimInfo result.alts optPreTac alts mkInitInfo stx[0]
          (numEqs := targets.size) (toClear := targetsNew) (toTag := toTag)

@[builtin_tactic Lean.Parser.Tactic.cases, builtin_incremental]
def evalCases : Tactic := fun stx =>
  match expandInduction? stx with
  | some stxNew => withMacroExpansion stx stxNew <| evalTactic stxNew
  | _ => focus do
    -- syntax (name := cases) "cases " elimTarget,+ (" using " term)? (inductionAlts)? : tactic
    let (targets, toTag) ← elabElimTargets stx[1].getSepArgs
    let elimInfo ← withMainContext <| getElimNameInfo stx[2] targets (induction := false)
    let targets ← withMainContext <| addImplicitTargets elimInfo targets
    evalCasesCore stx elimInfo targets toTag

@[builtin_tactic Lean.Parser.Tactic.funCases, builtin_incremental]
def evalFunCases : Tactic := fun stx =>
  match expandInduction? stx with
  | some stxNew => withMacroExpansion stx stxNew <| evalTactic stxNew
  | _ => focus do
    let (elimInfo, targets) ← elabFunTarget (cases := true) stx[1]
    let targets ← generalizeTargets targets
    evalCasesCore stx elimInfo targets

builtin_initialize
  registerTraceClass `Elab.cases
  registerTraceClass `Elab.induction

end Lean.Elab.Tactic
