/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Term
import Lean.Meta.RecursorInfo
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.ElimInfo
import Lean.Meta.Tactic.Induction
import Lean.Meta.Tactic.Cases
import Lean.Elab.App
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Generalize

namespace Lean.Elab.Tactic
open Meta

/-
  Given an `inductionAlt` of the form
  ```
  nodeWithAntiquot "inductionAlt" `Lean.Parser.Tactic.inductionAlt $ ident' >> many ident' >> darrow >> termParser
  ```
-/
private def getAltName (alt : Syntax) : Name :=
  getNameOfIdent' alt[1] |>.eraseMacroScopes
private def getAltVarNames (alt : Syntax) : Array Name :=
  alt[2].getArgs.map getNameOfIdent'
private def getAltRHS (alt : Syntax) : Syntax :=
  alt[4]
private def getAltDArrow (alt : Syntax) : Syntax :=
  alt[3]

-- Return true if `stx` is a term occurring in the RHS of the induction/cases tactic
def isHoleRHS (rhs : Syntax) : Bool :=
  rhs.isOfKind ``Parser.Term.syntheticHole || rhs.isOfKind ``Parser.Term.hole

def evalAlt (mvarId : MVarId) (alt : Syntax) (remainingGoals : Array MVarId) : TacticM (Array MVarId) :=
  withRef (getAltDArrow alt) do -- using `=>`'s position for error messages
    let rhs := getAltRHS alt
    if isHoleRHS rhs then
      let gs' ← withMVarContext mvarId $ withRef rhs do
        let mvarDecl ← getMVarDecl mvarId
        let val ← elabTermEnsuringType rhs mvarDecl.type
        assignExprMVar mvarId val
        let gs' ← getMVarsNoDelayed val
        tagUntaggedGoals mvarDecl.userName `induction gs'.toList
        pure gs'
      pure (remainingGoals ++ gs')
    else
      setGoals [mvarId]
      closeUsingOrAdmit rhs
      pure remainingGoals

/-
  Helper method for creating an user-defined eliminator/recursor application.
-/
namespace ElimApp

structure Context where
  elimInfo : ElimInfo
  targets  : Array Expr -- targets provided by the user

structure State where
  argPos    : Nat := 0 -- current argument position
  targetPos : Nat := 0 -- current target at targetsStx
  f         : Expr
  fType     : Expr
  alts      : Array (Name × MVarId) := #[]
  instMVars : Array MVarId := #[]

abbrev M := ReaderT Context $ StateRefT State TermElabM

private def addInstMVar (mvarId : MVarId) : M Unit :=
  modify fun s => { s with instMVars := s.instMVars.push mvarId }

private def addNewArg (arg : Expr) : M Unit :=
  modify fun s => { s with argPos := s.argPos+1, f := mkApp s.f arg, fType := s.fType.bindingBody!.instantiate1 arg }

/- Return the binder name at `fType`. This method assumes `fType` is a function type. -/
private def getBindingName : M Name := return (← get).fType.bindingName!
/- Return the next argument expected type. This method assumes `fType` is a function type. -/
private def getArgExpectedType : M Expr := return (← get).fType.bindingDomain!

private def getFType : M Expr := do
  let fType ← whnfForall (← get).fType
  modify fun s => { s with fType := fType }
  pure fType

structure Result where
  elimApp : Expr
  alts    : Array (Name × MVarId) := #[]

partial def mkElimApp (elimName : Name) (elimInfo : ElimInfo) (targets : Array Expr) (tag : Name) : TermElabM Result := do
  let rec loop : M Unit := do
    match (← getFType) with
    | Expr.forallE binderName _ _ c =>
      let ctx ← read
      let argPos := (← get).argPos
      if ctx.elimInfo.motivePos == argPos then
        let motive ← mkFreshExprMVar (← getArgExpectedType) MetavarKind.syntheticOpaque
        addNewArg motive
      else if ctx.elimInfo.targetsPos.contains argPos then
        if c.binderInfo.isExplicit then
          let s ← get
          let ctx ← read
          unless s.targetPos < ctx.targets.size do
            throwError! "insufficient number of targets for '{elimName}'"
          let target := ctx.targets[s.targetPos]
          let expectedType ← getArgExpectedType
          let target ← Term.ensureHasType expectedType target
          modify fun s => { s with targetPos := s.targetPos + 1 }
          addNewArg target
        else
          let target ← mkFreshExprMVar (← getArgExpectedType)
          addNewArg target
      else match c.binderInfo with
        | BinderInfo.implicit =>
          let arg ← mkFreshExprMVar (← getArgExpectedType)
          addNewArg arg
        | BinderInfo.instImplicit =>
          let arg ← mkFreshExprMVar (← getArgExpectedType) MetavarKind.synthetic
          addInstMVar arg.mvarId!
          addNewArg arg
        | _ =>
          let alt ← mkFreshExprSyntheticOpaqueMVar (← getArgExpectedType) (tag := appendTag tag binderName)
          modify fun s => { s with alts := s.alts.push (← getBindingName, alt.mvarId!) }
          addNewArg alt
      loop
    | _ =>
      pure ()
  let f ← Term.mkConst elimName
  let fType ← inferType f
  let (_, s) ← loop.run { elimInfo := elimInfo, targets := targets } |>.run { f := f, fType := fType }
  Lean.Elab.Term.synthesizeAppInstMVars s.instMVars
  pure { elimApp := (← instantiateMVars s.f), alts := s.alts }

/- Given a goal `... targets ... |- C[targets]` associated with `mvarId`, assign
  `motiveArg := fun targets => C[targets]` -/
def setMotiveArg (mvarId : MVarId) (motiveArg : MVarId) (targets : Array FVarId) : MetaM Unit := do
  let type ← inferType (mkMVar mvarId)
  let motive ← mkLambdaFVars (targets.map mkFVar) type
  let motiverInferredType ← inferType motive
  let motiveType ← inferType (mkMVar motiveArg)
  unless (← isDefEqGuarded motiverInferredType motiveType) do
    throwError! "type mismatch when assigning motive{indentExpr motive}\n{← mkHasTypeButIsExpectedMsg motiverInferredType motiveType}"
  assignExprMVar motiveArg motive

private def getAltNumFields (elimInfo : ElimInfo) (altName : Name) : TermElabM Nat := do
  for altInfo in elimInfo.altsInfo do
    if altInfo.name == altName then
      return altInfo.numFields
  throwError! "unknown alternative name '{altName}'"

private def checkAltNames (alts : Array (Name × MVarId)) (altsSyntax : Array Syntax) : TacticM Unit :=
  for altStx in altsSyntax do
    let altName := getAltName altStx
    if altName != `_ then
      unless alts.any fun (n, _) => n == altName do
        throwErrorAt! altStx "invalid alternative name '{altName}'"

def evalAlts (elimInfo : ElimInfo) (alts : Array (Name × MVarId)) (altsSyntax : Array Syntax)
    (numEqs : Nat := 0) (numGeneralized : Nat := 0) (toClear : Array FVarId := #[]) : TacticM Unit := do
  checkAltNames alts altsSyntax
  let mut usedWildcard := false
  let hasAlts := altsSyntax.size > 0
  let mut subgoals := #[] -- when alternatives are not provided, we accumulate subgoals here
  let mut altsSyntax := altsSyntax
  for (altName, altMVarId) in alts do
    let numFields ← getAltNumFields elimInfo altName
    let altStx? ←
      match altsSyntax.findIdx? (fun alt => getAltName alt == altName) with
      | some idx =>
        let altStx := altsSyntax[idx]
        altsSyntax := altsSyntax.eraseIdx idx
        pure (some altStx)
      | none => match altsSyntax.findIdx? (fun alt => getAltName alt == `_) with
        | some idx =>
          usedWildcard := true
          pure (some altsSyntax[idx])
        | none =>
          pure none
    match altStx? with
    | none =>
      let mut (_, altMVarId) ← introN altMVarId numFields
      match (← Cases.unifyEqs numEqs altMVarId {}) with
      | none   => pure () -- alternative is not reachable
      | some (altMVarId, _) =>
        if !hasAlts then
          -- User did not provide alternatives using `|`
          let (_, altMVarId) ← introNP altMVarId numGeneralized
          for fvarId in toClear do
            altMVarId ← tryClear altMVarId fvarId
          trace[Meta.debug]! "new subgoal {MessageData.ofGoal altMVarId}"
          subgoals := subgoals.push altMVarId
        else
          throwError! "alternative '{altName}' has not been provided"
    | some altStx =>
      subgoals ← withRef altStx do
        let altVarNames := getAltVarNames altStx
        let mut (_, altMVarId) ← introN altMVarId numFields altVarNames.toList
        match (← Cases.unifyEqs numEqs altMVarId {}) with
        | none   => throwError! "alternative '{altName}' is not needed"
        | some (altMVarId, _) =>
          let (_, altMVarId) ← introNP altMVarId numGeneralized
          for fvarId in toClear do
            altMVarId ← tryClear altMVarId fvarId
          evalAlt altMVarId altStx subgoals
  if usedWildcard then
    altsSyntax := altsSyntax.filter fun alt => getAltName alt != `_
  unless altsSyntax.isEmpty do
    throwErrorAt altsSyntax[0] "unused alternative"
  setGoals subgoals.toList

end ElimApp

/-
  Recall that
  ```
  generalizingVars := optional (" generalizing " >> many1 ident)
  «induction»  := parser! nonReservedSymbol "induction " >> majorPremise >> usingRec >> generalizingVars >> optional inductionAlts
  ```
  `stx` is syntax for `induction`. -/
private def getGeneralizingFVarIds (stx : Syntax) : TacticM (Array FVarId) :=
  withRef stx do
    let generalizingStx := stx[3]
    if generalizingStx.isNone then
      pure #[]
    else withMainMVarContext do
      trace `Elab.induction fun _ => generalizingStx
      let vars := generalizingStx[1].getArgs
      getFVarIds vars

-- process `generalizingVars` subterm of induction Syntax `stx`.
private def generalizeVars (stx : Syntax) (targets : Array Expr) : TacticM Nat := do
  let fvarIds ← getGeneralizingFVarIds stx
  liftMetaTacticAux fun mvarId => do
    let (fvarIds, mvarId') ← Meta.revert mvarId fvarIds
    if targets.any fun target => fvarIds.contains target.fvarId! then
      Meta.throwTacticEx `induction mvarId "major premise depends on variable being generalized"
    pure (fvarIds.size, [mvarId'])

private def getAltsOfInductionAlts (inductionAlts : Syntax) : Array Syntax :=
  inductionAlts[1].getArgs

private def getAltsOfOptInductionAlts (optInductionAlts : Syntax) : Array Syntax :=
  if optInductionAlts.isNone then #[] else getAltsOfInductionAlts optInductionAlts[0]

/-
  We may have at most one `| _ => ...` (wildcard alternative), and it must not set variable names.
  The idea is to make sure users do not write unstructured tactics. -/
private def checkAltsOfOptInductionAlts (optInductionAlts : Syntax) : TacticM Unit :=
  unless optInductionAlts.isNone do
    let mut found := false
    for alt in getAltsOfInductionAlts optInductionAlts[0] do
      let n := getAltName alt
      if n == `_ then
        unless (getAltVarNames alt).isEmpty do
          throwErrorAt! alt "wildcard alternative must not specify variable names"
        if found then
          throwErrorAt! alt "more than one wildcard alternative '| _ => ...' used"
        found := true

/-
  Given alts of the form
  ```
  nodeWithAntiquot "inductionAlt" `Lean.Parser.Tactic.inductionAlt $ ident' >> many ident' >> darrow >> termParser
  ```
  esnure the first `ident'` is `_` or a constructor name.
-/
private def checkAltCtorNames (alts : Array Syntax) (ctorNames : List Name) : TacticM Unit :=
  for alt in alts do
    let n := getAltName alt
    withRef alt $ trace[Elab.checkAlt]! "{n} , {alt}"
    unless n == `_ || ctorNames.any (fun ctorName => n.isSuffixOf ctorName) do
      throwErrorAt! alt[0] "invalid constructor name '{n}'"

structure RecInfo where
  recName : Name
  alts    : Array Syntax := #[] -- alternatives

def getInductiveValFromMajor (major : Expr) : TacticM InductiveVal :=
  liftMetaMAtMain fun mvarId => do
    let majorType ← inferType major
    let majorType ← whnf majorType
    matchConstInduct majorType.getAppFn
      (fun _ => Meta.throwTacticEx `induction mvarId m!"major premise type is not an inductive type {indentExpr majorType}")
      (fun val _ => pure val)

private partial def getRecFromUsingLoop (baseRecName : Name) (majorType : Expr) : TacticM (Option Meta.RecursorInfo) := do
  let finalize (majorType : Expr) : TacticM (Option Meta.RecursorInfo) := do
    let majorType? ← unfoldDefinition? majorType
    match majorType? with
    | some majorType => withIncRecDepth $ getRecFromUsingLoop baseRecName majorType
    | none           => pure none
  let majorType ← whnfCore majorType
  match majorType.getAppFn with
  | Expr.const name _ _ =>
    let candidate := name ++ baseRecName
    match (← getEnv).find? candidate with
    | some _ =>
      try
        liftMetaMAtMain fun _ => do
          let info ← Meta.mkRecursorInfo candidate
          pure (some info)
      catch _ =>
        finalize majorType
    | none   => finalize majorType
  | _ => finalize majorType

def getRecFromUsing (major : Expr) (baseRecName : Name) : TacticM Meta.RecursorInfo := do
  match ← getRecFromUsingLoop baseRecName (← inferType major) with
  | some recInfo => pure recInfo
  | none =>
    let recName ← resolveGlobalConstNoOverload baseRecName
    try
      liftMetaMAtMain fun _ => Meta.mkRecursorInfo recName
    catch _ =>
      throwError! "invalid recursor name '{baseRecName}'"

/- Create `RecInfo` assuming builtin recursor -/
private def getRecInfoDefault (major : Expr) (optInductionAlts : Syntax) (allowMissingAlts : Bool) : TacticM (RecInfo × Array Name) := do
  let indVal ← getInductiveValFromMajor major
  let recName := mkRecName indVal.name
  if optInductionAlts.isNone then
    pure ({ recName := recName }, #[])
  else
    let ctorNames   := indVal.ctors
    let alts        := getAltsOfInductionAlts optInductionAlts[0]
    checkAltCtorNames alts ctorNames
    let mut altsNew := #[]
    -- This code can be simplified if we decide to keep `checkAltsOfOptInductionAlts`
    let mut remainingAlts := alts
    let mut prevAnonymousAlt? := none
    for ctorName in ctorNames do
      match remainingAlts.findIdx? (fun alt => (getAltName alt).isSuffixOf ctorName) with
      | some idx =>
        let newAlt    := remainingAlts[idx]
        altsNew       := altsNew.push newAlt
        remainingAlts := remainingAlts.eraseIdx idx
      | none =>
          match remainingAlts.findIdx? (fun alt => getAltName alt == `_) with
          | some idx =>
            let newAlt        := remainingAlts[idx]
            altsNew           := altsNew.push newAlt
            remainingAlts     := remainingAlts.eraseIdx idx
            prevAnonymousAlt? := some newAlt
          | none => match prevAnonymousAlt? with
            | some alt => altsNew := altsNew.push alt
            | none     =>
              if allowMissingAlts then
                altsNew := altsNew.push Syntax.missing
              else
                throwError! "alternative for constructor '{ctorName}' is missing"
    unless remainingAlts.isEmpty do
      throwErrorAt remainingAlts[0] "unused alternative"
    pure ({ recName := recName, alts := altsNew }, ctorNames.toArray)

/-
  Recall that
  ```
  altRHS := Term.hole <|> Term.syntheticHole <|> tacticSeq
  inductionAlt  : Parser := parser! ident' >> many ident' >> darrow >> altRHS
  inductionAlts : Parser := parser! withPosition ("| " >> sepBy1 inductionAlt (checkColGe "alternatives must be indented" >> "|"))
  usingRec : Parser := optional (" using " >> ident)
  generalizingVars := optional (" generalizing " >> many1 ident)
  induction := parser! nonReservedSymbol "induction " >> sepBy1 termParser ", " >> usingRec >> generalizingVars >> optional inductionAlts
  ```
-/
private def getRecInfo (stx : Syntax) (major : Expr) : TacticM RecInfo := withRef stx $ withMainMVarContext do
  let usingRecStx := stx[2]
  let optInductionAlts := stx[4]
  checkAltsOfOptInductionAlts optInductionAlts
  if usingRecStx.isNone then
    let (rinfo, _) ← getRecInfoDefault major optInductionAlts false
    pure rinfo
  else
    let baseRecName := usingRecStx.getIdAt 1 |>.eraseMacroScopes
    let recInfo ← getRecFromUsing major baseRecName
    let recName := recInfo.recursorName
    if optInductionAlts.isNone then
      pure { recName := recName }
    else
      let alts := getAltsOfInductionAlts optInductionAlts[0]
      let paramNames ← liftMetaMAtMain fun _ => getParamNames recInfo.recursorName
      let mut remainingAlts     := alts
      let mut prevAnonymousAlt? := none
      let mut altsNew           := #[]
      for i in [:paramNames.size] do
        if recInfo.isMinor i then
          let paramName := paramNames[i]
          match remainingAlts.findIdx? (fun alt => getAltName alt == paramName) with
          | some idx =>
            let newAlt    := remainingAlts[idx]
            altsNew       := altsNew.push newAlt
            remainingAlts := remainingAlts.eraseIdx idx
          | none => match remainingAlts.findIdx? (fun alt => getAltName alt == `_) with
            | some idx =>
              let newAlt     := remainingAlts[idx]
              altsNew        := altsNew.push newAlt
              remainingAlts  := remainingAlts.eraseIdx idx
              prevAnonymousAlt? := some newAlt
            | none => match prevAnonymousAlt? with
              | some alt => altsNew := altsNew.push alt
              | none     => throwError! "alternative for minor premise '{paramName}' is missing"
      unless remainingAlts.isEmpty do
        throwErrorAt remainingAlts[0] "unused alternative"
      pure { recName := recName, alts := altsNew }

private def processResult (alts : Array Syntax) (result : Array Meta.InductionSubgoal) (numToIntro : Nat := 0) : TacticM Unit := do
  if alts.isEmpty then
    setGoals $ result.toList.map fun s => s.mvarId
  else
    unless alts.size == result.size do
      throwError! "mistmatch on the number of subgoals produced ({result.size}) and alternatives provided ({alts.size})"
    let mut gs := #[]
    for i in [:result.size] do
      let subgoal    := result[i]
      let mut mvarId := subgoal.mvarId
      if numToIntro > 0 then
        (_, mvarId) ← introNP mvarId numToIntro
      gs ← evalAlt mvarId alts[i] gs
    setGoals gs.toList

private def generalizeTerm (term : Expr) : TacticM Expr := do
  match term with
  | Expr.fvar .. => pure term
  | _ =>
    liftMetaTacticAux fun mvarId => do
      let mvarId ← Meta.generalize mvarId term `x false
      let (fvarId, mvarId) ← Meta.intro1 mvarId
      pure (mkFVar fvarId, [mvarId])

@[builtinTactic Lean.Parser.Tactic.induction] def evalInduction : Tactic := fun stx => focus do
  let targets ← stx[1].getSepArgs.mapM fun target => do
    let target ← withMainMVarContext $ elabTerm target none
    generalizeTerm target
  let n ← generalizeVars stx targets
  if targets.size == 1 then
    let recInfo ← getRecInfo stx targets[0]
    let (mvarId, _) ← getMainGoal
    let altVars := recInfo.alts.map fun alt => (getAltVarNames alt).toList
    let result ← Meta.induction mvarId targets[0].fvarId! recInfo.recName altVars
    processResult recInfo.alts result (numToIntro := n)
  else
    if stx[2].isNone then
      throwError! "eliminator must be provided when multiple targets are used (use 'using <eliminator-name>')"
    let elimId := stx[2][1]
    let elimName := elimId.getId
    let elimInfo ← withRef elimId do getElimInfo elimName
    let (mvarId, _) ← getMainGoal
    let tag ← getMVarTag mvarId
    withMVarContext mvarId do
      let result ← withRef stx[1] do -- use target position as reference
        ElimApp.mkElimApp elimName elimInfo targets tag
      assignExprMVar mvarId result.elimApp
      let elimArgs := result.elimApp.getAppArgs
      let targets ← elimInfo.targetsPos.mapM fun i => instantiateMVars elimArgs[i]
      let targetFVarIds := targets.map (·.fvarId!)
      ElimApp.setMotiveArg mvarId elimArgs[elimInfo.motivePos].mvarId! targetFVarIds
      let optInductionAlts := stx[4]
      ElimApp.evalAlts elimInfo result.alts (getAltsOfOptInductionAlts optInductionAlts) (numGeneralized := n) (toClear := targetFVarIds)

private partial def checkCasesResult (casesResult : Array Meta.CasesSubgoal) (ctorNames : Array Name) (alts : Array Syntax) : TacticM Unit := do
  let rec loop (i j : Nat) : TacticM Unit :=
    if h : j < alts.size then do
      let alt   := alts.get ⟨j, h⟩
      if alt.isMissing then
        loop i (j+1)
      else
        let ctorName := ctorNames.get! j
        if h : i < casesResult.size then
          let subgoal := casesResult.get ⟨i, h⟩
          if ctorName == subgoal.ctorName then
            loop (i+1) (j+1)
          else
            throwError! "alternative for '{subgoal.ctorName}' has not been provided"
        else
          throwError! "alternative for '{ctorName}' is not needed"
    else if h : i < casesResult.size then
      let subgoal := casesResult.get ⟨i, h⟩
      throwError! "alternative for '{subgoal.ctorName}' has not been provided"
    else
      pure ()
  unless alts.isEmpty do
    loop 0 0

-- Recall that
-- majorPremise := parser! optional (try (ident >> " : ")) >> termParser
private def getTargetHypothesisName? (target : Syntax) : Option Name :=
  if target[0].isNone then
    none
  else
    some target[0][0].getId

private def getTargetTerm (target : Syntax) : Syntax :=
  target[1]

private def elabTaggedTerm (h? : Option Name) (termStx : Syntax) : TacticM Expr :=
  withMainMVarContext $ withRef termStx do
    let term ← elabTerm termStx none
    match h? with
    | none   => pure term
    | some h =>
      let lctx ← getLCtx
      let x ← mkFreshUserName `x
      evalGeneralizeAux h? term x
      withMainMVarContext do
        let lctx ← getLCtx
        match lctx.findFromUserName? x with
        | some decl => pure decl.toExpr
        | none      => throwError "failed to generalize"

def elabTargets (targets : Array Syntax) : TacticM (Array Expr) :=
  targets.mapM fun target => do
    let h?    := getTargetHypothesisName? target
    let term ← elabTaggedTerm h? (getTargetTerm target)
    generalizeTerm term

builtin_initialize registerTraceClass `Elab.cases

/- Default `cases` tactic that uses `casesOn` eliminator -/
def evalCasesOn (target : Expr) (optInductionAlts : Syntax) : TacticM Unit := do
  let (mvarId, _) ← getMainGoal
  let (recInfo, ctorNames) ← getRecInfoDefault target optInductionAlts (allowMissingAlts := true)
  let altVars := recInfo.alts.map fun alt => (getAltVarNames alt).toList
  let result ← Meta.cases mvarId target.fvarId! altVars
  trace[Elab.cases]! "recInfo.alts.size: #{recInfo.alts.size} {recInfo.alts.map getAltVarNames}"
  trace[Elab.cases]! "recInfo.alts: #{recInfo.alts.map toString}"
  checkCasesResult result ctorNames recInfo.alts
  let result  := result.map (fun s => s.toInductionSubgoal)
  let alts := recInfo.alts.filter fun stx => !stx.isMissing
  processResult alts result

def evalCasesUsing (elimId : Syntax) (targetRef : Syntax) (targets : Array Expr) (optInductionAlts : Syntax) : TacticM Unit := do
  let elimName := elimId.getId
  let elimInfo ← withRef elimId do getElimInfo elimName
  let (mvarId, _) ← getMainGoal
  let tag ← getMVarTag mvarId
  withMVarContext mvarId do
    let result ← withRef targetRef $ ElimApp.mkElimApp elimName elimInfo targets tag
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM fun i => instantiateMVars elimArgs[i]
    let motiveType ← inferType elimArgs[elimInfo.motivePos]
    let mvarId ← generalizeTargets mvarId motiveType targets
    let (targetsNew, mvarId) ← introN mvarId targets.size
    withMVarContext mvarId do
      ElimApp.setMotiveArg mvarId elimArgs[elimInfo.motivePos].mvarId! targetsNew
      assignExprMVar mvarId result.elimApp
      ElimApp.evalAlts elimInfo result.alts (getAltsOfOptInductionAlts optInductionAlts) (numEqs := targets.size)

@[builtinTactic Lean.Parser.Tactic.cases] def evalCases : Tactic := fun stx => focus do
  -- parser! nonReservedSymbol "cases " >> sepBy1 (group majorPremise) ", " >> usingRec >> optInductionAlts
  let targets ← elabTargets stx[1].getSepArgs
  let optInductionAlts := stx[3]
  checkAltsOfOptInductionAlts optInductionAlts
  if stx[2].isNone then
    unless targets.size == 1 do
      throwErrorAt stx[1] "multiple targets are only supported when a user-defined eliminator is provided with 'using'"
    evalCasesOn targets[0] optInductionAlts
  else
    evalCasesUsing stx[2][1] (targetRef := stx[1]) targets optInductionAlts

end Lean.Elab.Tactic
