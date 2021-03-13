/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectMVars
import Lean.Parser.Command
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Subst
import Lean.Elab.Util
import Lean.Elab.Term
import Lean.Elab.Binders
namespace Lean.Elab
open Meta

def goalsToMessageData (goals : List MVarId) : MessageData :=
  MessageData.joinSep (goals.map $ MessageData.ofGoal) m!"\n\n"

def Term.reportUnsolvedGoals (goals : List MVarId) : TermElabM Unit := do
  throwError "unsolved goals\n{goalsToMessageData goals}"

namespace Tactic

structure Context where
  main : MVarId

structure State where
  goals : List MVarId
  deriving Inhabited

structure BacktrackableState where
  env   : Environment
  mctx  : MetavarContext
  term  : Term.State
  goals : List MVarId

abbrev TacticM := ReaderT Context $ StateRefT State TermElabM
abbrev Tactic  := Syntax → TacticM Unit

def saveBacktrackableState : TacticM BacktrackableState := do
  pure { env := (← getEnv), mctx := (← getMCtx), term := (← getThe Term.State), goals := (← get).goals }

def BacktrackableState.restore (b : BacktrackableState) : TacticM Unit := do
  setEnv b.env
  setMCtx b.mctx
  let infoState ← getInfoState -- we do not backtrack info state
  let msgLog ← Term.getMessageLog -- we do not backtrack the message log
  set b.term
  Term.setMessageLog msgLog
  modifyInfoState fun _ => infoState
  modify fun s => { s with goals := b.goals }

@[inline] protected def tryCatch {α} (x : TacticM α) (h : Exception → TacticM α) : TacticM α := do
  let b ← saveBacktrackableState
  try x catch ex => b.restore; h ex

instance : MonadExcept Exception TacticM where
  throw    := throw
  tryCatch := Tactic.tryCatch

@[inline] protected def orElse {α} (x y : TacticM α) : TacticM α := do
  try x catch _ => y

instance {α} : OrElse (TacticM α) where
  orElse := Tactic.orElse

structure SavedState where
  core   : Core.State
  meta   : Meta.State
  term   : Term.State
  tactic : State
  deriving Inhabited

def saveAllState : TacticM SavedState := do
  pure { core := (← getThe Core.State), meta := (← getThe Meta.State), term := (← getThe Term.State), tactic := (← get) }

def SavedState.restore (s : SavedState) : TacticM Unit := do
  set s.core; set s.meta; set s.term; set s.tactic

def withoutModifyingState (x : TacticM α) : TacticM α := do
  let s ← saveAllState
  try x finally s.restore

protected def getCurrMacroScope : TacticM MacroScope := do pure (← readThe Term.Context).currMacroScope
protected def getMainModule     : TacticM Name       := do pure (← getEnv).mainModule

unsafe def mkTacticAttribute : IO (KeyedDeclsAttribute Tactic) :=
  mkElabAttribute Tactic `Lean.Elab.Tactic.tacticElabAttribute `builtinTactic `tactic `Lean.Parser.Tactic `Lean.Elab.Tactic.Tactic "tactic"

@[builtinInit mkTacticAttribute] constant tacticElabAttribute : KeyedDeclsAttribute Tactic

private def evalTacticUsing (s : SavedState) (stx : Syntax) (tactics : List Tactic) : TacticM Unit := do
  let rec loop : List Tactic → TacticM Unit
    | []              => throwErrorAt stx "unexpected syntax {indentD stx}"
    | evalFn::evalFns => do
      try
        evalFn stx
      catch
      | ex@(Exception.error _ _) =>
        match evalFns with
        | []      => throw ex
        | evalFns => s.restore; loop evalFns
      | ex@(Exception.internal id _) =>
        if id == unsupportedSyntaxExceptionId then
          s.restore; loop evalFns
        else
          throw ex
  loop tactics

def getGoals : TacticM (List MVarId) := do pure (← get).goals

mutual

  partial def expandTacticMacroFns (stx : Syntax) (macros : List Macro) : TacticM Unit :=
    let rec loop : List Macro → TacticM Unit
      | []    => throwErrorAt stx "tactic '{stx.getKind}' has not been implemented"
      | m::ms => do
        let scp ← getCurrMacroScope
        try
          let stx' ← adaptMacro m stx
          evalTactic stx'
        catch ex =>
          if ms.isEmpty then throw ex
          loop ms
    loop macros

  partial def expandTacticMacro (stx : Syntax) : TacticM Unit := do
    let k        := stx.getKind
    let table    := (macroAttribute.ext.getState (← getEnv)).table
    let macroFns := (table.find? k).getD []
    expandTacticMacroFns stx macroFns

  partial def evalTacticAux (stx : Syntax) : TacticM Unit :=
    withRef stx $ withIncRecDepth $ withFreshMacroScope $ match stx with
      | Syntax.node k args =>
        if k == nullKind then
          -- Macro writers create a sequence of tactics `t₁ ... tₙ` using `mkNullNode #[t₁, ..., tₙ]`
          stx.getArgs.forM evalTactic
        else do
          trace `Elab.step fun _ => stx
          let env ← getEnv
          let s ← saveAllState
          let table := (tacticElabAttribute.ext.getState env).table
          let k := stx.getKind
          match table.find? k with
          | some evalFns => evalTacticUsing s stx evalFns
          | none         => expandTacticMacro stx
      | _ => throwError "unexpected command"

  partial def mkTacticInfo (mctxBefore : MetavarContext) (goalsBefore : List MVarId) (stx : Syntax) : TacticM Info :=
    return Info.ofTacticInfo {
      mctxBefore    := mctxBefore
      goalsBefore   := goalsBefore
      stx           := stx
      mctxAfter     := (← getMCtx)
      goalsAfter    := (← getGoals)
    }

  partial def evalTactic (stx : Syntax) : TacticM Unit := do
    let mctxBefore  ← getMCtx
    let goalsBefore ← getGoals
    withInfoContext (evalTacticAux stx) (mkTacticInfo mctxBefore goalsBefore stx)

end

/- Elaborate `x` with `stx` on the macro stack -/
@[inline]
def withMacroExpansion {α} (beforeStx afterStx : Syntax) (x : TacticM α) : TacticM α :=
  withMacroExpansionInfo beforeStx afterStx do
    withTheReader Term.Context (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

/-- Adapt a syntax transformation to a regular tactic evaluator. -/
def adaptExpander (exp : Syntax → TacticM Syntax) : Tactic := fun stx => do
  let stx' ← exp stx
  withMacroExpansion stx stx' $ evalTactic stx'

def setGoals (gs : List MVarId) : TacticM Unit := modify $ fun s => { s with goals := gs }

def appendGoals (gs : List MVarId) : TacticM Unit := modify $ fun s => { s with goals := s.goals ++ gs }

def pruneSolvedGoals : TacticM Unit := do
  let gs ← getGoals
  let gs ← gs.filterM fun g => not <$> isExprMVarAssigned g
  setGoals gs

def getUnsolvedGoals : TacticM (List MVarId) := do pruneSolvedGoals; getGoals

def getMainGoal : TacticM (MVarId × List MVarId) := do let (g::gs) ← getUnsolvedGoals | throwError "no goals to be solved"; pure (g, gs)

def getMainTag : TacticM Name := do
  let (g, _) ← getMainGoal
  pure (← getMVarDecl g).userName

/- Evaluate `tac` at `mvarId`, and return the list of resulting subgoals. -/
def evalTacticAt (tac : Syntax) (mvarId : MVarId) : TacticM (List MVarId) := do
  let gs ← getGoals
  try
    setGoals [mvarId]
    evalTactic tac
    pruneSolvedGoals
    getGoals
  finally
    setGoals gs

def ensureHasNoMVars (e : Expr) : TacticM Unit := do
  let e ← instantiateMVars e
  let pendingMVars ← getMVars e
  discard <| Term.logUnassignedUsingErrorInfos pendingMVars
  if e.hasExprMVar then
    throwError "tactic failed, resulting expression contains metavariables{indentExpr e}"

def withMainMVarContext {α} (x : TacticM α) : TacticM α := do
  let (mvarId, _) ← getMainGoal
  withMVarContext mvarId x

@[inline] def liftMetaMAtMain {α} (x : MVarId → MetaM α) : TacticM α := do
  let (g, _) ← getMainGoal
  withMVarContext g <| x g

@[inline] def liftMetaTacticAux {α} (tactic : MVarId → MetaM (α × List MVarId)) : TacticM α := do
  let (g, gs) ← getMainGoal
  withMVarContext g do
    let (a, gs') ← tactic g
    setGoals (gs' ++ gs)
    pure a

@[inline] def liftMetaTactic (tactic : MVarId → MetaM (List MVarId)) : TacticM Unit :=
  liftMetaTacticAux fun mvarId => do
    let gs ← tactic mvarId
    pure ((), gs)

def done : TacticM Unit := do
  let gs ← getUnsolvedGoals;
  unless gs.isEmpty do
    Term.reportUnsolvedGoals gs

@[builtinTactic Lean.Parser.Tactic.«done»] def evalDone : Tactic := fun _ => done

def focus {α} (tactic : TacticM α) : TacticM α := do
  let (g, gs) ← getMainGoal
  setGoals [g]
  let a ← tactic
  let gs' ← getGoals
  setGoals (gs' ++ gs)
  pure a

def focusAndDone {α} (tactic : TacticM α) : TacticM α :=
  focus do let a ← tactic; done; pure a

/- Assign `mvarId := sorry` -/
def admitGoal (mvarId : MVarId) : TacticM Unit := do
  let mvarType ← inferType (mkMVar mvarId)
  assignExprMVar mvarId (← mkSorry mvarType (synthetic := true))

/- Close the main goal using the given tactic. If it fails, log the error and `admit` -/
def closeUsingOrAdmit (tac : Syntax) : TacticM Unit := do
  let (mvarId, rest) ← getMainGoal
  try
    evalTactic tac
    done
  catch ex =>
    logException ex
    admitGoal mvarId
    setGoals rest

def try? {α} (tactic : TacticM α) : TacticM (Option α) := do
  try pure (some (← tactic))
  catch _ => pure none

-- TODO: rename?
def «try» {α} (tactic : TacticM α) : TacticM Bool := do
  try
    discard tactic
    pure true
  catch _ =>
    pure false

/--
  Use `parentTag` to tag untagged goals at `newGoals`.
  If there are multiple new untagged goals, they are named using `<parentTag>.<newSuffix>_<idx>` where `idx > 0`.
  If there is only one new untagged goal, then we just use `parentTag` -/
def tagUntaggedGoals (parentTag : Name) (newSuffix : Name) (newGoals : List MVarId) : TacticM Unit := do
  let mctx ← getMCtx
  let mut numAnonymous := 0
  for g in newGoals do
    if mctx.isAnonymousMVar g then
      numAnonymous := numAnonymous + 1
  modifyMCtx fun mctx => do
    let mut mctx := mctx
    let mut idx  := 1
    for g in newGoals do
      if mctx.isAnonymousMVar g then
        if numAnonymous == 1 then
          mctx := mctx.renameMVar g parentTag
        else
          mctx := mctx.renameMVar g (parentTag ++ newSuffix.appendIndexAfter idx)
        idx := idx + 1
    pure mctx

@[builtinTactic seq1] def evalSeq1 : Tactic := fun stx =>
  stx[0].getSepArgs.forM evalTactic

@[builtinTactic paren] def evalParen : Tactic := fun stx =>
  evalTactic stx[1]

@[builtinTactic tacticSeq1Indented] def evalTacticSeq1Indented : Tactic := fun stx =>
  stx[0].forArgsM fun seqElem => evalTactic seqElem[0]

@[builtinTactic tacticSeqBracketed] def evalTacticSeqBracketed : Tactic := fun stx =>
  withRef stx[2] <| focusAndDone <| stx[1].forArgsM fun seqElem => evalTactic seqElem[0]

@[builtinTactic Parser.Tactic.focus] def evalFocus : Tactic := fun stx =>
  focus <| evalTactic stx[1]

private def getOptRotation (stx : Syntax) : Nat :=
  if stx.isNone then 1 else stx[0].toNat

@[builtinTactic Parser.Tactic.rotateLeft] def evalRotateLeft : Tactic := fun stx => do
  let n := getOptRotation stx[1]
  setGoals <| (← getGoals).rotateLeft n

@[builtinTactic Parser.Tactic.rotateRight] def evalRotateRight : Tactic := fun stx => do
  let n := getOptRotation stx[1]
  setGoals <| (← getGoals).rotateRight n

@[builtinTactic Parser.Tactic.open] def evalOpen : Tactic := fun stx => do
  let openDecls ← elabOpenDecl stx[1]
  withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
    evalTactic stx[3]

@[builtinTactic Parser.Tactic.set_option] def elabSetOption : Tactic := fun stx => do
  let options ← Elab.elabSetOption stx[1] stx[2]
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := maxRecDepth.get options, options := options }) do
    evalTactic stx[4]

@[builtinTactic Parser.Tactic.allGoals] def evalAllGoals : Tactic := fun stx => do
  let gs ← getUnsolvedGoals
  let mut gsNew := []
  for g in gs do
    unless ← isExprMVarAssigned g do
      setGoals [g]
      evalTactic stx[1]
      gsNew := gsNew ++ (← getUnsolvedGoals)
  setGoals gsNew

@[builtinTactic tacticSeq] def evalTacticSeq : Tactic := fun stx =>
  evalTactic stx[0]

partial def evalChoiceAux (tactics : Array Syntax) (i : Nat) : TacticM Unit :=
  if h : i < tactics.size then
    let tactic := tactics.get ⟨i, h⟩
    catchInternalId unsupportedSyntaxExceptionId
      (evalTactic tactic)
      (fun _ => evalChoiceAux tactics (i+1))
  else
    throwUnsupportedSyntax

@[builtinTactic choice] def evalChoice : Tactic := fun stx =>
  evalChoiceAux stx.getArgs 0

@[builtinTactic skip] def evalSkip : Tactic := fun stx => pure ()

@[builtinTactic failIfSuccess] def evalFailIfSuccess : Tactic := fun stx => do
  let tactic := stx[1]
  if (← try evalTactic tactic; pure true catch _ => pure false) then
    throwError "tactic succeeded"

@[builtinTactic traceState] def evalTraceState : Tactic := fun stx => do
  let gs ← getUnsolvedGoals
  logInfo (goalsToMessageData gs)

@[builtinTactic Lean.Parser.Tactic.assumption] def evalAssumption : Tactic := fun stx =>
  liftMetaTactic fun mvarId => do Meta.assumption mvarId; pure []

@[builtinTactic Lean.Parser.Tactic.contradiction] def evalContradiction : Tactic := fun stx =>
  liftMetaTactic fun mvarId => do Meta.contradiction mvarId; pure []

@[builtinTactic Lean.Parser.Tactic.intro] def evalIntro : Tactic := fun stx => do
  match stx with
  | `(tactic| intro)                   => introStep `_
  | `(tactic| intro $h:ident)          => introStep h.getId
  | `(tactic| intro _)                 => introStep `_
  | `(tactic| intro $pat:term)         => evalTactic (← `(tactic| intro h; match h with | $pat:term => _; try clear h))
  | `(tactic| intro $h:term $hs:term*) => evalTactic (← `(tactic| intro $h:term; intro $hs:term*))
  | _ => throwUnsupportedSyntax
where
  introStep (n : Name) : TacticM Unit :=
    liftMetaTactic fun mvarId => do
      let (_, mvarId) ← Meta.intro mvarId n
      pure [mvarId]

@[builtinTactic Lean.Parser.Tactic.introMatch] def evalIntroMatch : Tactic := fun stx => do
  let matchAlts := stx[1]
  let stxNew ← liftMacroM <| Term.expandMatchAltsIntoMatchTactic stx matchAlts
  withMacroExpansion stx stxNew <| evalTactic stxNew

private def getIntrosSize : Expr → Nat
  | Expr.forallE _ _ b _ => getIntrosSize b + 1
  | Expr.letE _ _ _ b _  => getIntrosSize b + 1
  | _                    => 0

/- Recall that `ident' := ident <|> Term.hole` -/
def getNameOfIdent' (id : Syntax) : Name :=
  if id.isIdent then id.getId else `_

@[builtinTactic «intros»] def evalIntros : Tactic := fun stx =>
  match stx with
  | `(tactic| intros)       => liftMetaTactic fun mvarId => do
    let type ← Meta.getMVarType mvarId
    let type ← instantiateMVars type
    let n := getIntrosSize type
    let (_, mvarId) ← Meta.introN mvarId n
    pure [mvarId]
  | `(tactic| intros $ids*) => liftMetaTactic fun mvarId => do
    let (_, mvarId) ← Meta.introN mvarId ids.size (ids.map getNameOfIdent').toList
    pure [mvarId]
  | _                       => throwUnsupportedSyntax

def getFVarId (id : Syntax) : TacticM FVarId := withRef id do
  let fvar? ← Term.isLocalIdent? id;
  match fvar? with
  | some fvar => pure fvar.fvarId!
  | none      => throwError "unknown variable '{id.getId}'"

def getFVarIds (ids : Array Syntax) : TacticM (Array FVarId) := do
  withMainMVarContext $ ids.mapM getFVarId

@[builtinTactic Lean.Parser.Tactic.revert] def evalRevert : Tactic := fun stx =>
  match stx with
  | `(tactic| revert $hs*) => do
     let (g, gs) ← getMainGoal
     let fvarIds ← getFVarIds hs
     let (_, g) ← Meta.revert g fvarIds
     setGoals (g :: gs)
  | _                     => throwUnsupportedSyntax

/- Sort free variables using an order `x < y` iff `x` was defined after `y` -/
private def sortFVarIds (fvarIds : Array FVarId) : TacticM (Array FVarId) :=
  withMainMVarContext do
    let lctx ← getLCtx
    pure $ fvarIds.qsort fun fvarId₁ fvarId₂ =>
      match lctx.find? fvarId₁, lctx.find? fvarId₂ with
      | some d₁, some d₂ => d₁.index > d₂.index
      | some _,  none    => false
      | none,    some _  => true
      | none,    none    => Name.quickLt fvarId₁ fvarId₂

@[builtinTactic Lean.Parser.Tactic.clear] def evalClear : Tactic := fun stx =>
  match stx with
  | `(tactic| clear $hs*) => do
    let fvarIds ← getFVarIds hs
    let fvarIds ← sortFVarIds fvarIds
    for fvarId in fvarIds do
      let (g, gs) ← getMainGoal
      withMVarContext g do
        let g ← clear g fvarId
        setGoals (g :: gs)
  | _ => throwUnsupportedSyntax

def forEachVar (hs : Array Syntax) (tac : MVarId → FVarId → MetaM MVarId) : TacticM Unit := do
  for h in hs do
    let (g, gs) ← getMainGoal;
    withMVarContext g do
      let fvarId ← getFVarId h
      let g ← tac g fvarId
      setGoals (g :: gs)

@[builtinTactic Lean.Parser.Tactic.subst] def evalSubst : Tactic := fun stx =>
  match stx with
  | `(tactic| subst $hs*) => forEachVar hs Meta.subst
  | _                     => throwUnsupportedSyntax

/--
  First method searches for a metavariable `g` s.t. `tag` is a suffix of its name.
  If none is found, then it searches for a metavariable `g` s.t. `tag` is a prefix of its name. -/
private def findTag? (gs : List MVarId) (tag : Name) : TacticM (Option MVarId) := do
  let g? ← gs.findM? (fun g => do pure $ tag.isSuffixOf (← getMVarDecl g).userName);
  match g? with
  | some g => pure g
  | none   => gs.findM? (fun g => do pure $ tag.isPrefixOf (← getMVarDecl g).userName)

@[builtinTactic «case»] def evalCase : Tactic := fun stx =>
  match stx with
  | `(tactic| case $tag => $tac:tacticSeq) => do
     let tag := tag.getId
     let gs ← getUnsolvedGoals
     let some g ← findTag? gs tag | throwError "tag not found"
     let gs := gs.erase g
     setGoals [g]
     let savedTag ← getMVarTag g
     setMVarTag g Name.anonymous
     try
       closeUsingOrAdmit tac
     finally
       setMVarTag g savedTag
     done
     setGoals gs
  | _ => throwUnsupportedSyntax

@[builtinTactic «first»] partial def evalFirst : Tactic := fun stx => do
  let tacs := stx[2].getSepArgs
  if tacs.isEmpty then throwUnsupportedSyntax
  loop tacs 0
where
  loop (tacs : Array Syntax) (i : Nat) :=
    if i == tacs.size - 1 then
      evalTactic tacs[i]
    else
      evalTactic tacs[i] <|> loop tacs (i+1)

builtin_initialize registerTraceClass `Elab.tactic

@[inline] def TacticM.run {α} (x : TacticM α) (ctx : Context) (s : State) : TermElabM (α × State) :=
  x ctx |>.run s

@[inline] def TacticM.run' {α} (x : TacticM α) (ctx : Context) (s : State) : TermElabM α :=
  Prod.fst <$> x.run ctx s

end Lean.Elab.Tactic
