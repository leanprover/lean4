/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
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
  ``` -/
private def getAltName (alt : Syntax) : Name := alt[0].getId.eraseMacroScopes
private def getAltVarNames (alt : Syntax) : Array Name := alt[1].getArgs.map Syntax.getId
private def getAltRHS (alt : Syntax) : Syntax := alt[3]

/-
  Helper method for creating an user-defined eliminator/recursor application.
-/
namespace ElimApp

structure Context :=
  (elimInfo    : ElimInfo)
  (targetTerms : Array Syntax) -- targets provided by the user

structure State :=
  (argPos    : Nat := 0) -- current argument position
  (targetPos : Nat := 0) -- current target at targetsStx
  (f         : Expr)
  (fType     : Expr)
  (alts      : Array (Name × MVarId) := #[])
  (instMVars : Array MVarId := #[])

abbrev M := ReaderT Context $ StateRefT State TermElabM

private def addInstMVar (mvarId : MVarId) : M Unit :=
  modify fun s => { s with instMVars := s.instMVars.push mvarId }

private def addNewArg (arg : Expr) : M Unit :=
  modify fun s => { s with argPos := s.argPos+1, f := mkApp s.f arg, fType := s.fType.bindingBody!.instantiate1 arg }

/- Return the binder name at `fType`. This method assumes `fType` is a function type. -/
private def getBindingName : M Name := return (← get).fType.bindingName!
/- Return the next argument expected type. This method assumes `fType` is a function type. -/
private def getArgExpectedType : M Expr := return (← get).fType.bindingDomain!

private def elabNextTarget : M Unit := do
  unless (← get).targetPos < (← read).targetTerms.size do
    throwError! "invalid 'eliminate', insufficient number of targets"
  let target ← Term.elabTerm (← read).targetTerms[(← get).targetPos] (← getArgExpectedType)
  modify fun s => { s with targetPos := s.targetPos + 1 }
  addNewArg target

private def getFType : M Expr := do
  let fType ← whnfForall (← get).fType
  modify fun s => { s with fType := fType }
  pure fType

structure Result :=
  (elimApp : Expr)
  (alts    : Array (Name × MVarId) := #[])

partial def mkElimApp (elimName : Name) (elimInfo : ElimInfo) (targetTerms : Array Syntax) (tag : Name) : TermElabM Result := do
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
          elabNextTarget
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
  let (_, s) ← loop.run { elimInfo := elimInfo, targetTerms := targetTerms } $.run { f := f, fType := fType }
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
    throwError! "type mismatch when assigning motive{indentExpr motive}\nhas type{indentExpr motiverInferredType}\nexpected type{indentExpr motiveType}"
  assignExprMVar motiveArg motive

private def getAltNumFields (elimInfo : ElimInfo) (altName : Name) : TermElabM Nat := do
  for altInfo in elimInfo.altsInfo do
    if altInfo.name == altName then
      return altInfo.numFields
  throwError! "unknown alternative name '{altName}'"

def evalAlts (elimInfo : ElimInfo) (alts : Array (Name × MVarId)) (altsSyntax : Array Syntax)
    (numEqs : Nat := 0) (numGeneralized : Nat := 0) : TacticM Unit := do
  let usedWildcard := false
  let hasAlts      := altsSyntax.size > 0
  let subgoals     := #[] -- when alternatives are not provided, we accumulate subgoals here
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
      let (_, altMVarId) ← introN altMVarId numFields
      match (← Cases.unifyEqs numEqs altMVarId {}) with
      | none   => pure () -- alternative is not reachable
      | some (altMVarId, _) =>
        if !hasAlts then
          -- User did not provide alternatives using `|`
          let (_, altMVarId) ← introNP altMVarId numGeneralized
          trace[Meta.debug]! "new subgoal {MessageData.ofGoal altMVarId}"
          subgoals := subgoals.push altMVarId
        else
          throwError! "alternative '{altName}' has not been provided"
    | some altStx => withRef altStx do
      let altRhs := getAltRHS altStx
      let altVarNames := getAltVarNames altStx
      let (_, altMVarId) ← introN altMVarId numFields altVarNames.toList
      match (← Cases.unifyEqs numEqs altMVarId {}) with
      | none   => throwError! "alternative '{altName}' is not needed"
      | some (altMVarId, _) =>
        let (_, altMVarId) ← introNP altMVarId numGeneralized
        setGoals [altMVarId]
        evalTactic altRhs
        done
  if usedWildcard then
    altsSyntax := altsSyntax.filter fun alt => getAltName alt != `_
  unless altsSyntax.isEmpty do
    throwErrorAt altsSyntax[0] "unused alternative"
  setGoals subgoals.toList

end ElimApp

-- Recall that
-- majorPremise := parser! optional (try (ident >> " : ")) >> termParser
private def getTargetHypothesisName? (target : Syntax) : Option Name :=
  if target[0].isNone then
    none
  else
    some target[0][0].getId

private def getTargetTerm (target : Syntax) : Syntax :=
  target[1]

private def elabMajor (h? : Option Name) (major : Syntax) : TacticM Expr := do
  match h? with
  | none   => withMainMVarContext $ elabTerm major none
  | some h => withMainMVarContext do
    let lctx ← getLCtx
    let x ← mkFreshUserName `x
    let major ← elabTerm major none
    evalGeneralizeAux h? major x
    withMainMVarContext do
      let lctx ← getLCtx
      match lctx.findFromUserName? x with
      | some decl => pure decl.toExpr
      | none      => throwError "failed to generalize"

private def generalizeMajor (major : Expr) : TacticM Expr := do
  match major with
  | Expr.fvar _ _ => pure major
  | _ =>
    liftMetaTacticAux fun mvarId => do
      mvarId ← Meta.generalize mvarId major `x false
      let (fvarId, mvarId) ← Meta.intro1 mvarId
      pure (mkFVar fvarId, [mvarId])

/-
  Recall that
  ```
  generalizingVars := optional (" generalizing " >> many1 ident)
  «induction»  := parser! nonReservedSymbol "induction " >> majorPremise >> usingRec >> generalizingVars >> withAlts
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
private def generalizeVars (stx : Syntax) (major : Expr) : TacticM Nat := do
  let fvarIds ← getGeneralizingFVarIds stx
  liftMetaTacticAux fun mvarId => do
    let (fvarIds, mvarId') ← Meta.revert mvarId fvarIds
    if fvarIds.contains major.fvarId! then
      Meta.throwTacticEx `induction mvarId "major premise depends on variable being generalized"
    pure (fvarIds.size, [mvarId'])

private def getAlts (withAlts : Syntax) : Array Syntax :=
  withAlts[1].getSepArgs

/-
  We may have at most one `| _ => ...` (wildcard alternative), and it must not set variable names.
  The idea is to make sure users do not write unstructured tactics. -/
private def checkAlts (withAlts : Syntax) : TacticM Unit := do
  let found := false
  for alt in getAlts withAlts do
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

structure RecInfo :=
  (recName : Name)
  (altVars : Array (List Name) := #[]) -- new variable names for each minor premise
  (altRHSs : Array Syntax := #[])      -- RHS for each minor premise

def getInductiveValFromMajor (major : Expr) : TacticM InductiveVal :=
  liftMetaMAtMain fun mvarId => do
    let majorType ← inferType major
    let majorType ← whnf majorType
    matchConstInduct majorType.getAppFn
      (fun _ => Meta.throwTacticEx `induction mvarId msg!"major premise type is not an inductive type {indentExpr majorType}")
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
private def getRecInfoDefault (major : Expr) (withAlts : Syntax) (allowMissingAlts : Bool) : TacticM (RecInfo × Array Name) := do
  let indVal ← getInductiveValFromMajor major
  let recName := mkRecName indVal.name
  if withAlts.isNone then
    pure ({ recName := recName }, #[])
  else
    let ctorNames := indVal.ctors
    let alts      := getAlts withAlts
    checkAltCtorNames alts ctorNames
    let altVars := #[]
    let altRHSs := #[]
    -- This code can be simplified if we decide to keep `checkAlts`
    let remainingAlts := alts
    let prevAnonymousAlt? := none
    for ctorName in ctorNames do
      match remainingAlts.findIdx? (fun alt => (getAltName alt).isSuffixOf ctorName) with
      | some idx =>
        let newAlt := remainingAlts[idx]
        altVars       := altVars.push (getAltVarNames newAlt).toList
        altRHSs       := altRHSs.push (getAltRHS newAlt)
        remainingAlts := remainingAlts.eraseIdx idx
      | none =>
          match remainingAlts.findIdx? (fun alt => getAltName alt == `_) with
          | some idx =>
            let newAlt        := remainingAlts[idx]
            altVars           := altVars.push (getAltVarNames newAlt).toList
            altRHSs           := altRHSs.push (getAltRHS newAlt)
            remainingAlts     := remainingAlts.eraseIdx idx
            prevAnonymousAlt? := some newAlt
          | none => match prevAnonymousAlt? with
            | some alt =>
              altVars := altVars.push (getAltVarNames alt).toList
              altRHSs := altRHSs.push (getAltRHS alt)
            | none     =>
              if allowMissingAlts then
                altVars := altVars.push []
                altRHSs := altRHSs.push Syntax.missing
              else
                throwError! "alternative for constructor '{ctorName}' is missing"
    unless remainingAlts.isEmpty do
      throwErrorAt remainingAlts[0] "unused alternative"
    pure ({ recName := recName, altVars := altVars, altRHSs := altRHSs }, ctorNames.toArray)

/-
  Recall that
  ```
  inductionAlt  : Parser :=
    nodeWithAntiquot "inductionAlt" `Lean.Parser.Tactic.inductionAlt $ ident' >> many ident' >> darrow >> (hole <|> syntheticHole <|> tacticParser)
  inductionAlts : Parser := withPosition $ fun pos => "|" >> sepBy1 inductionAlt (checkColGe pos.column "alternatives must be indented" >> "|")
  withAlts : Parser := optional (" with " >> inductionAlts)
  usingRec : Parser := optional (" using " >> ident)
  ``` -/
private def getRecInfo (stx : Syntax) (major : Expr) : TacticM RecInfo := withRef stx $ withMainMVarContext do
  let usingRecStx := stx[2]
  let withAlts    := stx[4]
  checkAlts withAlts
  if usingRecStx.isNone then
    let (rinfo, _) ← getRecInfoDefault major withAlts false
    pure rinfo
  else
    let baseRecName := usingRecStx.getIdAt 1 $.eraseMacroScopes
    let recInfo ← getRecFromUsing major baseRecName
    let recName := recInfo.recursorName
    if withAlts.isNone then
      pure { recName := recName }
    else
      let alts := getAlts withAlts
      let paramNames ← liftMetaMAtMain fun _ => getParamNames recInfo.recursorName
      let altVars           := #[]
      let altRHSs           := #[]
      let remainingAlts     := alts
      let prevAnonymousAlt? := none
      for i in [:paramNames.size] do
        if recInfo.isMinor i then
          let paramName := paramNames[i]
          match remainingAlts.findIdx? (fun alt => getAltName alt == paramName) with
          | some idx =>
            let newAlt := remainingAlts[idx]
            altVars := altVars.push (getAltVarNames newAlt).toList
            altRHSs := altRHSs.push (getAltRHS newAlt)
            remainingAlts := remainingAlts.eraseIdx idx
          | none => match remainingAlts.findIdx? (fun alt => getAltName alt == `_) with
            | some idx =>
              let newAlt     := remainingAlts[idx]
              altVars := altVars.push (getAltVarNames newAlt).toList
              altRHSs := altRHSs.push (getAltRHS newAlt)
              remainingAlts := remainingAlts.eraseIdx idx
              prevAnonymousAlt? := some newAlt
            | none => match prevAnonymousAlt? with
              | some alt =>
                altVars := altVars.push (getAltVarNames alt).toList
                altRHSs := altRHSs.push (getAltRHS alt)
              | none     =>
                throwError! "alternative for minor premise '{paramName}' is missing"
      unless remainingAlts.isEmpty do
        throwErrorAt remainingAlts[0] "unused alternative"
      pure { recName := recName, altVars := altVars, altRHSs := altRHSs }

-- Return true if `stx` is a term occurring in the RHS of the induction/cases tactic
def isHoleRHS (rhs : Syntax) : Bool :=
  rhs.isOfKind `Lean.Parser.Term.syntheticHole || rhs.isOfKind `Lean.Parser.Term.hole

private def processResult (altRHSs : Array Syntax) (result : Array Meta.InductionSubgoal) (numToIntro : Nat := 0) : TacticM Unit := do
  if altRHSs.isEmpty then
    setGoals $ result.toList.map fun s => s.mvarId
  else
    unless altRHSs.size == result.size do
      throwError! "mistmatch on the number of subgoals produced ({result.size}) and alternatives provided ({altRHSs.size})"
    let gs := []
    for i in [:result.size] do
      let subgoal := result[i]
      let rhs     := altRHSs[i]
      let ref     := rhs
      let mvarId  := subgoal.mvarId
      if numToIntro > 0 then
        (_, mvarId) ← introNP mvarId numToIntro
      if isHoleRHS rhs then
        let gs' ← withMVarContext mvarId $ withRef rhs do
          let mvarDecl ← getMVarDecl mvarId
          let val ← elabTermEnsuringType rhs mvarDecl.type
          assignExprMVar mvarId val
          let gs' ← getMVarsNoDelayed val
          let gs' := gs'.toList
          tagUntaggedGoals mvarDecl.userName `induction gs'
          pure gs'
        gs := gs ++ gs'
      else
        setGoals [mvarId]
        evalTactic rhs
        done
    setGoals gs

@[builtinTactic Lean.Parser.Tactic.induction] def evalInduction : Tactic := fun stx => focusAux do
  let targets := stx[1].getSepArgs
  if targets.size == 1 then
    let target := targets[0]
    let h? := getTargetHypothesisName? target
    let major ← elabMajor h? (getTargetTerm target)
    let major ← generalizeMajor major
    let n ← generalizeVars stx major
    let recInfo ← getRecInfo stx major
    let (mvarId, _) ← getMainGoal
    let result ← Meta.induction mvarId major.fvarId! recInfo.recName recInfo.altVars
    processResult recInfo.altRHSs result (numToIntro := n)
  else
    throwError! "WIP"

private partial def checkCasesResult (casesResult : Array Meta.CasesSubgoal) (ctorNames : Array Name) (altRHSs : Array Syntax) : TacticM Unit := do
  let rec loop (i j : Nat) : TacticM Unit :=
    if h : j < altRHSs.size then do
      let altRHS   := altRHSs.get ⟨j, h⟩
      if altRHS.isMissing then
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
  unless altRHSs.isEmpty do
    loop 0 0

/- Default `cases` tactic that uses `casesOn` eliminator -/
def evalCasesOn (target : Syntax) (withAlts : Syntax) : TacticM Unit := do
  let h?    := getTargetHypothesisName? target
  let major ← elabMajor h? (getTargetTerm target)
  let major ← generalizeMajor major
  let (mvarId, _) ← getMainGoal
  let (recInfo, ctorNames) ← getRecInfoDefault major withAlts true
  let result ← Meta.cases mvarId major.fvarId! recInfo.altVars
  checkCasesResult result ctorNames recInfo.altRHSs
  let result  := result.map (fun s => s.toInductionSubgoal)
  let altRHSs := recInfo.altRHSs.filter fun stx => !stx.isMissing
  processResult altRHSs result

def evalCasesUsing (targets : Array Syntax) (elimName : Name) (withAlts : Syntax) : TacticM Unit := do
  let elimInfo ← getElimInfo elimName
  let (mvarId, _) ← getMainGoal
  let tag ← getMVarTag mvarId
  withMVarContext mvarId do
    let result ← ElimApp.mkElimApp elimName elimInfo (targets.map (·[1])) tag
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM fun i => instantiateMVars elimArgs[i]
    let motiveType ← inferType elimArgs[elimInfo.motivePos]
    let mvarId ← generalizeTargets mvarId motiveType targets
    let (targetsNew, mvarId) ← introN mvarId targets.size
    withMVarContext mvarId do
      ElimApp.setMotiveArg mvarId elimArgs[elimInfo.motivePos].mvarId! targetsNew
      assignExprMVar mvarId result.elimApp
      ElimApp.evalAlts elimInfo result.alts (getAlts withAlts) (numEqs := targets.size)

@[builtinTactic Lean.Parser.Tactic.cases] def evalCases : Tactic := fun stx => focusAux do
  -- parser! nonReservedSymbol "cases " >> sepBy1 (group majorPremise) ", " >> usingRec >> withAlts
  let targets  := stx[1].getSepArgs
  let withAlts := stx[3]
  checkAlts withAlts
  if stx[2].isNone then
    unless targets.size == 1 do
      throwErrorAt targets[1] "multiple targets are only supported when a user-defined eliminator is provided with 'using'"
    evalCasesOn targets[0] withAlts
  else
    evalCasesUsing targets stx[2][1].getId withAlts

end Lean.Elab.Tactic
