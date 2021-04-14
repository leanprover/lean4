/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectFVars
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
  -- alt[1] is of the form (("@"? ident) <|> "_")
  if alt[1].hasArgs then alt[1][1].getId.eraseMacroScopes else `_
private def altHasExplicitModifier (alt : Syntax) : Bool :=
  alt[1].hasArgs && !alt[1][0].isNone
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
  let rhs := getAltRHS alt
  withCaseRef (getAltDArrow alt) rhs do
    if isHoleRHS rhs then
      let gs' ← withMVarContext mvarId $ withRef rhs do
        let mvarDecl ← getMVarDecl mvarId
        let val ← elabTermEnsuringType rhs mvarDecl.type
        assignExprMVar mvarId val
        let gs' ← getMVarsNoDelayed val
        tagUntaggedGoals mvarDecl.userName `induction gs'.toList
        pure gs'
      return remainingGoals ++ gs'
    else
      setGoals [mvarId]
      closeUsingOrAdmit rhs
      return remainingGoals

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
  insts     : Array MVarId := #[]

abbrev M := ReaderT Context $ StateRefT State TermElabM

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
  others  : Array MVarId := #[]

/--
  Construct the an eliminator/recursor application. `targets` contains the explicit and implicit targets for
  the eliminator. For example, the indices of builtin recursors are considered implicit targets.
  Remark: the method `addImplicitTargets` may be used to compute the sequence of implicit and explicit targets
  from the explicit ones.
-/
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
        let s ← get
        let ctx ← read
        unless s.targetPos < ctx.targets.size do
          throwError "insufficient number of targets for '{elimName}'"
        let target := ctx.targets[s.targetPos]
        let expectedType ← getArgExpectedType
        let target ← Term.ensureHasType expectedType target
        modify fun s => { s with targetPos := s.targetPos + 1 }
        addNewArg target
      else match c.binderInfo with
        | BinderInfo.implicit =>
          let arg ← mkFreshExprMVar (← getArgExpectedType)
          addNewArg arg
        | BinderInfo.instImplicit =>
          let arg ← mkFreshExprMVar (← getArgExpectedType) (kind := MetavarKind.synthetic) (userName := appendTag tag binderName)
          modify fun s => { s with insts := s.insts.push arg.mvarId! }
          addNewArg arg
        | _ =>
          let arg ← mkFreshExprSyntheticOpaqueMVar (← getArgExpectedType) (tag := appendTag tag binderName)
          modify fun s => { s with alts := s.alts.push (← getBindingName, arg.mvarId!) }
          addNewArg arg
      loop
    | _ =>
      pure ()
  let f ← Term.mkConst elimName
  let fType ← inferType f
  let (_, s) ← loop.run { elimInfo := elimInfo, targets := targets } |>.run { f := f, fType := fType }
  let mut others := #[]
  for mvarId in s.insts do
    try
      unless (← Term.synthesizeInstMVarCore mvarId) do
        setMVarKind mvarId MetavarKind.syntheticOpaque
        others := others.push mvarId
    catch _ =>
      setMVarKind mvarId MetavarKind.syntheticOpaque
      others := others.push mvarId
  return { elimApp := (← instantiateMVars s.f), alts := s.alts, others := others }

/- Given a goal `... targets ... |- C[targets]` associated with `mvarId`, assign
  `motiveArg := fun targets => C[targets]` -/
def setMotiveArg (mvarId : MVarId) (motiveArg : MVarId) (targets : Array FVarId) : MetaM Unit := do
  let type ← inferType (mkMVar mvarId)
  let motive ← mkLambdaFVars (targets.map mkFVar) type
  let motiverInferredType ← inferType motive
  let motiveType ← inferType (mkMVar motiveArg)
  unless (← isDefEqGuarded motiverInferredType motiveType) do
    throwError "type mismatch when assigning motive{indentExpr motive}\n{← mkHasTypeButIsExpectedMsg motiverInferredType motiveType}"
  assignExprMVar motiveArg motive

private def getAltNumFields (elimInfo : ElimInfo) (altName : Name) : TermElabM Nat := do
  for altInfo in elimInfo.altsInfo do
    if altInfo.name == altName then
      return altInfo.numFields
  throwError "unknown alternative name '{altName}'"

private def checkAltNames (alts : Array (Name × MVarId)) (altsSyntax : Array Syntax) : TacticM Unit :=
  for altStx in altsSyntax do
    let altName := getAltName altStx
    if altName != `_ then
      unless alts.any fun (n, _) => n == altName do
        throwErrorAt altStx "invalid alternative name '{altName}'"

def evalAlts (elimInfo : ElimInfo) (alts : Array (Name × MVarId)) (optPreTac : Syntax) (altsSyntax : Array Syntax)
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
        let (_, altMVarId) ← introNP altMVarId numGeneralized
        for fvarId in toClear do
          altMVarId ← tryClear altMVarId fvarId
        let altMVarIds ← applyPreTac altMVarId
        if !hasAlts then
          -- User did not provide alternatives using `|`
          subgoals := subgoals ++ altMVarIds.toArray
        else if altMVarIds.isEmpty then
          pure ()
        else
          logError m!"alternative '{altName}' has not been provided"
          altMVarIds.forM admitGoal
    | some altStx =>
      subgoals ← withRef altStx do
        let altVarNames := getAltVarNames altStx
        if altVarNames.size > numFields then
          logError m!"too many variable names provided at alternative '{altName}', #{altVarNames.size} provided, but #{numFields} expected"
        let mut (_, altMVarId) ← introN altMVarId numFields altVarNames.toList (useNamesForExplicitOnly := !altHasExplicitModifier altStx)
        match (← Cases.unifyEqs numEqs altMVarId {}) with
        | none   => throwError "alternative '{altName}' is not needed"
        | some (altMVarId, _) =>
          let (_, altMVarId) ← introNP altMVarId numGeneralized
          for fvarId in toClear do
            altMVarId ← tryClear altMVarId fvarId
          let altMVarIds ← applyPreTac altMVarId
          if altMVarIds.isEmpty then
            throwError "alternative '{altName}' is not needed"
          else
            altMVarIds.foldlM (init := subgoals) fun subgoal altMVarId =>
              evalAlt altMVarId altStx subgoals
  if usedWildcard then
    altsSyntax := altsSyntax.filter fun alt => getAltName alt != `_
  unless altsSyntax.isEmpty do
    logErrorAt altsSyntax[0] "unused alternative"
  setGoals subgoals.toList
where
  applyPreTac (mvarId : MVarId) : TacticM (List MVarId) :=
    if optPreTac.isNone then
      return [mvarId]
    else
      evalTacticAt optPreTac[0] mvarId

end ElimApp

/--
  Return a set of `FVarId`s containing `targets` and all variables they depend on.

  Remark: this method assumes `targets` are free variables.
-/
private partial def mkForbiddenSet (targets : Array Expr) : MetaM NameSet := do
  loop (targets.toList.map Expr.fvarId!) {}
where
  visit (fvarId : FVarId) (todo : List FVarId) (s : NameSet) : MetaM (List FVarId × NameSet) := do
    let localDecl ← getLocalDecl fvarId
    let mut s' := collectFVars {} (← instantiateMVars localDecl.type)
    if let some val := localDecl.value? then
      s' := collectFVars s' (← instantiateMVars val)
    let mut todo := todo
    let mut s := s
    for fvarId in s'.fvarSet do
      unless s.contains fvarId do
        todo := fvarId :: todo
        s := s.insert fvarId
    return (todo, s)

  loop (todo : List FVarId) (s : NameSet) : MetaM NameSet := do
    match todo with
    | [] => return s
    | fvarId::todo =>
      if s.contains fvarId then
        loop todo s
      else
        let (todo, s) ← visit fvarId todo <| s.insert fvarId
        loop todo s

/--
  Collect forward dependencies that are not in the forbidden set, and depend on some variable in `targets`.

  Remark: this method assumes `targets` are free variables.

  Remark: we *not* collect instance implicit arguments nor auxiliary declarations for compiling
  recursive declarations.
-/
private def collectForwardDeps (targets : Array Expr) (forbidden : NameSet) : MetaM NameSet := do
  let mut s : NameSet := targets.foldl (init := {}) fun s target => s.insert target.fvarId!
  let mut r : NameSet := {}
  for localDecl in (← getLCtx) do
    unless forbidden.contains localDecl.fvarId do
      unless localDecl.isAuxDecl || localDecl.binderInfo.isInstImplicit do
      if (← getMCtx).findLocalDeclDependsOn localDecl fun fvarId => s.contains fvarId then
        r := r.insert localDecl.fvarId
        s := s.insert localDecl.fvarId
  return r

/-
  Recall that
  ```
  generalizingVars := optional (" generalizing " >> many1 ident)
  «induction»  := leading_parser nonReservedSymbol "induction " >> majorPremise >> usingRec >> generalizingVars >> optional inductionAlts
  ```
  `stx` is syntax for `induction`. -/
private def getGeneralizingFVarIds (stx : Syntax) : TacticM (Array FVarId) :=
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
  withMVarContext mvarId do
    let userFVarIds ← getGeneralizingFVarIds stx
    let forbidden ← mkForbiddenSet targets
    let mut s ← collectForwardDeps targets forbidden
    for userFVarId in userFVarIds do
      if forbidden.contains userFVarId then
        throwError "variable cannot be generalized because target depends on it{indentExpr (mkFVar userFVarId)}"
      if s.contains userFVarId then
        throwError "unnecessary 'generalizing' argument, variable '{mkFVar userFVarId}' is generalized automatically"
      s := s.insert userFVarId
    let fvarIds := s.fold (init := #[]) fun s fvarId => s.push fvarId
    let lctx ← getLCtx
    let fvarIds ← fvarIds.qsort fun x y => (lctx.get! x).index < (lctx.get! y).index
    let (fvarIds, mvarId') ← Meta.revert mvarId fvarIds
    return (fvarIds.size, mvarId')

-- syntax inductionAlts := "with " (tactic)? withPosition( (colGe inductionAlt)+)
private def getAltsOfInductionAlts (inductionAlts : Syntax) : Array Syntax :=
  inductionAlts[2].getArgs

private def getAltsOfOptInductionAlts (optInductionAlts : Syntax) : Array Syntax :=
  if optInductionAlts.isNone then #[] else getAltsOfInductionAlts optInductionAlts[0]

private def getOptPreTacOfOptInductionAlts (optInductionAlts : Syntax) : Syntax :=
  if optInductionAlts.isNone then mkNullNode else optInductionAlts[0][1]

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

private def generalizeTerm (term : Expr) : TacticM Expr := do
  match term with
  | Expr.fvar .. => pure term
  | _ =>
    liftMetaTacticAux fun mvarId => do
      let mvarId ← Meta.generalize mvarId term `x false
      let (fvarId, mvarId) ← Meta.intro1 mvarId
      pure (mkFVar fvarId, [mvarId])

-- `optElimId` is of the form `("using" ident)?`
private def getElimNameInfo (optElimId : Syntax) (targets : Array Expr) (induction : Bool): TacticM (Name × ElimInfo) := do
  if optElimId.isNone then
    unless targets.size == 1 do
      throwError "eliminator must be provided when multiple targets are used (use 'using <eliminator-name>')"
    let indVal ← getInductiveValFromMajor targets[0]
    let elimName := if induction then mkRecName indVal.name else mkCasesOnName indVal.name
    pure (elimName, ← getElimInfo elimName)
  else
    let elimId := optElimId[1]
    let elimName ← withRef elimId do resolveGlobalConstNoOverloadWithInfo elimId elimId.getId.eraseMacroScopes
    pure (elimName, ← withRef elimId do getElimInfo elimName)

@[builtinTactic Lean.Parser.Tactic.induction] def evalInduction : Tactic := fun stx => focus do
  let targets ← stx[1].getSepArgs.mapM fun target => do
    let target ← withMainContext <| elabTerm target none
    generalizeTerm target
  let (elimName, elimInfo) ← getElimNameInfo stx[2] targets (induction := true)
  let mvarId ← getMainGoal
  let tag ← getMVarTag mvarId
  withMVarContext mvarId do
    let targets ← addImplicitTargets elimInfo targets
    checkTargets targets
    let targetFVarIds := targets.map (·.fvarId!)
    let (n, mvarId) ← generalizeVars mvarId stx targets
    withMVarContext mvarId do
      let result ← withRef stx[1] do -- use target position as reference
        ElimApp.mkElimApp elimName elimInfo targets tag
      let elimArgs := result.elimApp.getAppArgs
      let motiveType ← inferType elimArgs[elimInfo.motivePos]
      ElimApp.setMotiveArg mvarId elimArgs[elimInfo.motivePos].mvarId! targetFVarIds
      let optInductionAlts := stx[4]
      let optPreTac := getOptPreTacOfOptInductionAlts optInductionAlts
      let alts := getAltsOfOptInductionAlts optInductionAlts
      assignExprMVar mvarId result.elimApp
      ElimApp.evalAlts elimInfo result.alts optPreTac alts (numGeneralized := n) (toClear := targetFVarIds)
      appendGoals result.others.toList
where
  checkTargets (targets : Array Expr) : MetaM Unit := do
    let mut foundFVars : NameSet := {}
    for target in targets do
      unless target.isFVar do
        throwError "index in target's type is not a variable (consider using the `cases` tactic instead){indentExpr target}"
      if foundFVars.contains target.fvarId! then
        throwError "target (or one of its indices) occurs more than once{indentExpr target}"

-- Recall that
-- majorPremise := leading_parser optional (try (ident >> " : ")) >> termParser
private def getTargetHypothesisName? (target : Syntax) : Option Name :=
  if target[0].isNone then
    none
  else
    some target[0][0].getId

private def getTargetTerm (target : Syntax) : Syntax :=
  target[1]

private def elabTaggedTerm (h? : Option Name) (termStx : Syntax) : TacticM Expr :=
  withMainContext <| withRef termStx do
    let term ← elabTerm termStx none
    match h? with
    | none   => pure term
    | some h =>
      let lctx ← getLCtx
      let x ← mkFreshUserName `x
      evalGeneralizeAux h? term x
      withMainContext do
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

@[builtinTactic Lean.Parser.Tactic.cases] def evalCases : Tactic := fun stx => focus do
  -- leading_parser nonReservedSymbol "cases " >> sepBy1 (group majorPremise) ", " >> usingRec >> optInductionAlts
  let targets ← elabTargets stx[1].getSepArgs
  let optInductionAlts := stx[3]
  let optPreTac := getOptPreTacOfOptInductionAlts optInductionAlts
  let alts :=  getAltsOfOptInductionAlts optInductionAlts
  let targetRef := stx[1]
  let (elimName, elimInfo) ← getElimNameInfo stx[2] targets (induction := false)
  let mvarId ← getMainGoal
  let tag ← getMVarTag mvarId
  withMVarContext mvarId do
    let targets ← addImplicitTargets elimInfo targets
    let result ← withRef targetRef <| ElimApp.mkElimApp elimName elimInfo targets tag
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM fun i => instantiateMVars elimArgs[i]
    let motiveType ← inferType elimArgs[elimInfo.motivePos]
    let mvarId ← generalizeTargets mvarId motiveType targets
    let (targetsNew, mvarId) ← introN mvarId targets.size
    withMVarContext mvarId do
      ElimApp.setMotiveArg mvarId elimArgs[elimInfo.motivePos].mvarId! targetsNew
      assignExprMVar mvarId result.elimApp
      ElimApp.evalAlts elimInfo result.alts optPreTac alts (numEqs := targets.size) (toClear := targetsNew)

end Lean.Elab.Tactic
