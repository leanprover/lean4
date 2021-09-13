/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectMVars
import Lean.Parser.Command
import Lean.Meta.PPGoal
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

/- Assign `mvarId := sorry` -/
def admitGoal (mvarId : MVarId) : MetaM Unit :=
  withMVarContext mvarId do
    let mvarType ← inferType (mkMVar mvarId)
    assignExprMVar mvarId (← mkSorry mvarType (synthetic := true))

def goalsToMessageData (goals : List MVarId) : MessageData :=
  MessageData.joinSep (goals.map $ MessageData.ofGoal) m!"\n\n"

def Term.reportUnsolvedGoals (goals : List MVarId) : TermElabM Unit :=
  withPPInaccessibleNames do
    logError <| MessageData.tagged `Tactic.unsolvedGoals <| m!"unsolved goals\n{goalsToMessageData goals}"
    goals.forM fun mvarId => admitGoal mvarId

namespace Tactic

structure Context where
  main       : MVarId
  -- declaration name of the executing elaborator, used by `mkTacticInfo` to persist it in the info tree
  elaborator : Name

structure State where
  goals : List MVarId
  deriving Inhabited

structure SavedState where
  term   : Term.SavedState
  tactic : State

abbrev TacticM := ReaderT Context $ StateRefT State TermElabM
abbrev Tactic  := Syntax → TacticM Unit

-- Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
-- whole monad stack at every use site. May eventually be covered by `deriving`.
instance : Monad TacticM := let i := inferInstanceAs (Monad TacticM); { pure := i.pure, bind := i.bind }

def getGoals : TacticM (List MVarId) :=
  return (← get).goals

def setGoals (mvarIds : List MVarId) : TacticM Unit :=
  modify fun s => { s with goals := mvarIds }

def pruneSolvedGoals : TacticM Unit := do
  let gs ← getGoals
  let gs ← gs.filterM fun g => not <$> isExprMVarAssigned g
  setGoals gs

def getUnsolvedGoals : TacticM (List MVarId) := do
  pruneSolvedGoals
  getGoals

@[inline] private def TacticM.runCore (x : TacticM α) (ctx : Context) (s : State) : TermElabM (α × State) :=
  x ctx |>.run s

@[inline] private def TacticM.runCore' (x : TacticM α) (ctx : Context) (s : State) : TermElabM α :=
  Prod.fst <$> x.runCore ctx s

def run (mvarId : MVarId) (x : TacticM Unit) : TermElabM (List MVarId) :=
  withMVarContext mvarId do
   let savedSyntheticMVars := (← get).syntheticMVars
   modify fun s => { s with syntheticMVars := [] }
   let aux : TacticM (List MVarId) :=
     /- Important: the following `try` does not backtrack the state.
        This is intentional because we don't want to backtrack the error messages when we catch the "abort internal exception"
        We must define `run` here because we define `MonadExcept` instance for `TacticM` -/
     try
       x; getUnsolvedGoals
     catch ex =>
       if isAbortTacticException ex then
         getUnsolvedGoals
       else
         throw ex
   try
     aux.runCore' { main := mvarId, elaborator := Name.anonymous } { goals := [mvarId] }
   finally
     modify fun s => { s with syntheticMVars := savedSyntheticMVars }

protected def saveState : TacticM SavedState :=
  return { term := (← Term.saveState), tactic := (← get) }

def SavedState.restore (b : SavedState) : TacticM Unit := do
  b.term.restore
  set b.tactic

protected def getCurrMacroScope : TacticM MacroScope := do pure (← readThe Term.Context).currMacroScope
protected def getMainModule     : TacticM Name       := do pure (← getEnv).mainModule

unsafe def mkTacticAttribute : IO (KeyedDeclsAttribute Tactic) :=
  mkElabAttribute Tactic `Lean.Elab.Tactic.tacticElabAttribute `builtinTactic `tactic `Lean.Parser.Tactic `Lean.Elab.Tactic.Tactic "tactic"

@[builtinInit mkTacticAttribute] constant tacticElabAttribute : KeyedDeclsAttribute Tactic

def mkTacticInfo (mctxBefore : MetavarContext) (goalsBefore : List MVarId) (stx : Syntax) : TacticM Info :=
  return Info.ofTacticInfo {
    elaborator    := (← read).elaborator
    mctxBefore    := mctxBefore
    goalsBefore   := goalsBefore
    stx           := stx
    mctxAfter     := (← getMCtx)
    goalsAfter    := (← getUnsolvedGoals)
  }

def mkInitialTacticInfo (stx : Syntax) : TacticM (TacticM Info) := do
  let mctxBefore  ← getMCtx
  let goalsBefore ← getUnsolvedGoals
  return mkTacticInfo mctxBefore goalsBefore stx

@[inline] def withTacticInfoContext (stx : Syntax) (x : TacticM α) : TacticM α := do
  withInfoContext x (← mkInitialTacticInfo stx)

/-
Important: we must define `evalTacticUsing` and `expandTacticMacroFns` before we define
the instance `MonadExcept` for `TacticM` since it backtracks the state including error messages,
and this is bad when rethrowing the exception at the `catch` block in these methods.
We marked these places with a `(*)` in these methods.
-/

private def evalTacticUsing (s : SavedState) (stx : Syntax) (tactics : List (KeyedDeclsAttribute.AttributeEntry Tactic)) : TacticM Unit := do
  let rec loop
    | []              => throwErrorAt stx "unexpected syntax {indentD stx}"
    | evalFn::evalFns => do
      try
        withReader ({ · with elaborator := evalFn.declName }) <| withTacticInfoContext stx <| evalFn.value stx
      catch
      | ex@(Exception.error _ _) =>
        match evalFns with
        | []      => throw ex -- (*)
        | evalFns => s.restore; loop evalFns
      | ex@(Exception.internal id _) =>
        if id == unsupportedSyntaxExceptionId then
          s.restore; loop evalFns
        else
          throw ex
  loop tactics

mutual

  partial def expandTacticMacroFns (stx : Syntax) (macros : List (KeyedDeclsAttribute.AttributeEntry Macro)) : TacticM Unit :=
    let rec loop
      | []    => throwErrorAt stx "tactic '{stx.getKind}' has not been implemented"
      | m::ms => do
        let scp ← getCurrMacroScope
        try
          withReader ({ · with elaborator := m.declName }) do
            withTacticInfoContext stx do
              let stx' ← adaptMacro m.value stx
              evalTactic stx'
        catch ex =>
          if ms.isEmpty then throw ex -- (*)
          loop ms
    loop macros

  partial def expandTacticMacro (stx : Syntax) : TacticM Unit := do
    expandTacticMacroFns stx (macroAttribute.getEntries (← getEnv) stx.getKind)

  partial def evalTacticAux (stx : Syntax) : TacticM Unit :=
    withRef stx $ withIncRecDepth $ withFreshMacroScope $ match stx with
      | Syntax.node k args =>
        if k == nullKind then
          -- Macro writers create a sequence of tactics `t₁ ... tₙ` using `mkNullNode #[t₁, ..., tₙ]`
          stx.getArgs.forM evalTactic
        else do
          trace[Elab.step] "{stx}"
          let s ← Tactic.saveState
          match tacticElabAttribute.getEntries (← getEnv) stx.getKind with
          | []      => expandTacticMacro stx
          | evalFns => evalTacticUsing s stx evalFns
      | _ => throwError m!"unexpected tactic{indentD stx}"

  partial def evalTactic (stx : Syntax) : TacticM Unit :=
    evalTacticAux stx

end

def throwNoGoalsToBeSolved : TacticM α :=
  throwError "no goals to be solved"

def done : TacticM Unit := do
  let gs ← getUnsolvedGoals
  unless gs.isEmpty do
    Term.reportUnsolvedGoals gs
    throwAbortTactic

def focus (x : TacticM α) : TacticM α := do
  let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved
  setGoals [mvarId]
  let a ← x
  let mvarIds' ← getUnsolvedGoals
  setGoals (mvarIds' ++ mvarIds)
  pure a

def focusAndDone (tactic : TacticM α) : TacticM α :=
  focus do
    let a ← tactic
    done
    pure a

/- Close the main goal using the given tactic. If it fails, log the error and `admit` -/
def closeUsingOrAdmit (tac : TacticM Unit) : TacticM Unit := do
  /- Important: we must define `closeUsingOrAdmit` before we define
     the instance `MonadExcept` for `TacticM` since it backtracks the state including error messages. -/
  let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved
  try
    focusAndDone tac
  catch ex =>
    logException ex
    admitGoal mvarId
    setGoals mvarIds

instance : MonadBacktrack SavedState TacticM where
  saveState := Tactic.saveState
  restoreState b := b.restore

@[inline] protected def tryCatch {α} (x : TacticM α) (h : Exception → TacticM α) : TacticM α := do
  let b ← saveState
  try x catch ex => b.restore; h ex

instance : MonadExcept Exception TacticM where
  throw    := throw
  tryCatch := Tactic.tryCatch

@[inline] protected def orElse {α} (x : TacticM α) (y : Unit → TacticM α) : TacticM α := do
  try x catch _ => y ()

instance {α} : OrElse (TacticM α) where
  orElse := Tactic.orElse

instance : Alternative TacticM where
  failure := fun {α} => throwError "failed"
  orElse  := Tactic.orElse

/-
  Save the current tactic state for a token `stx`.
  This method is a no-op if `stx` has no position information.
  We use this method to save the tactic state at punctuation such as `;`
-/
def saveTacticInfoForToken (stx : Syntax) : TacticM Unit := do
  unless stx.getPos?.isNone do
    withTacticInfoContext stx (pure ())

/- Elaborate `x` with `stx` on the macro stack -/
@[inline]
def withMacroExpansion {α} (beforeStx afterStx : Syntax) (x : TacticM α) : TacticM α :=
  withMacroExpansionInfo beforeStx afterStx do
    withTheReader Term.Context (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

/-- Adapt a syntax transformation to a regular tactic evaluator. -/
def adaptExpander (exp : Syntax → TacticM Syntax) : Tactic := fun stx => do
  let stx' ← exp stx
  withMacroExpansion stx stx' $ evalTactic stx'

def appendGoals (mvarIds : List MVarId) : TacticM Unit :=
  modify fun s => { s with goals := s.goals ++ mvarIds }

def replaceMainGoal (mvarIds : List MVarId) : TacticM Unit := do
  let (mvarId :: mvarIds') ← getGoals | throwNoGoalsToBeSolved
  modify fun s => { s with goals := mvarIds ++ mvarIds' }

/-- Return the first goal. -/
def getMainGoal : TacticM MVarId := do
  loop (← getGoals)
where
  loop : List MVarId → TacticM MVarId
    | [] => throwNoGoalsToBeSolved
    | mvarId :: mvarIds => do
      if (← isExprMVarAssigned mvarId) then
        loop mvarIds
      else
        setGoals (mvarId :: mvarIds)
        return mvarId

/-- Return the main goal metavariable declaration. -/
def getMainDecl : TacticM MetavarDecl := do
  getMVarDecl (← getMainGoal)

/-- Return the main goal tag. -/
def getMainTag : TacticM Name :=
  return (← getMainDecl).userName

/-- Return expected type for the main goal. -/
def getMainTarget : TacticM Expr := do
  instantiateMVars (← getMainDecl).type

/-- Execute `x` using the main goal local context and instances -/
def withMainContext (x : TacticM α) : TacticM α := do
  withMVarContext (← getMainGoal) x

/-- Evaluate `tac` at `mvarId`, and return the list of resulting subgoals. -/
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

/-- Close main goal using the given expression. If `checkUnassigned == true`, then `val` must not contain unassinged metavariables. -/
def closeMainGoal (val : Expr) (checkUnassigned := true): TacticM Unit := do
  if checkUnassigned then
    ensureHasNoMVars val
  assignExprMVar (← getMainGoal) val
  replaceMainGoal []

@[inline] def liftMetaMAtMain (x : MVarId → MetaM α) : TacticM α := do
  withMainContext do x (← getMainGoal)

@[inline] def liftMetaTacticAux (tac : MVarId → MetaM (α × List MVarId)) : TacticM α := do
  withMainContext do
    let (a, mvarIds) ← tac (← getMainGoal)
    replaceMainGoal mvarIds
    pure a

@[inline] def liftMetaTactic (tactic : MVarId → MetaM (List MVarId)) : TacticM Unit :=
  liftMetaTacticAux fun mvarId => do
    let gs ← tactic mvarId
    pure ((), gs)

@[inline] def liftMetaTactic1 (tactic : MVarId → MetaM (Option MVarId)) : TacticM Unit :=
  withMainContext do
    if let some mvarId ← tactic (← getMainGoal) then
      replaceMainGoal [mvarId]
    else
      replaceMainGoal []

def tryTactic? (tactic : TacticM α) : TacticM (Option α) := do
  try
    pure (some (← tactic))
  catch _ =>
    pure none

def tryTactic (tactic : TacticM α) : TacticM Bool := do
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

/- Recall that `ident' := ident <|> Term.hole` -/
def getNameOfIdent' (id : Syntax) : Name :=
  if id.isIdent then id.getId else `_

def getFVarId (id : Syntax) : TacticM FVarId := withRef id do
  let fvar? ← Term.isLocalIdent? id;
  match fvar? with
  | some fvar => pure fvar.fvarId!
  | none      => throwError "unknown variable '{id.getId}'"

def getFVarIds (ids : Array Syntax) : TacticM (Array FVarId) := do
  withMainContext do ids.mapM getFVarId

/--
  Use position of `=> $body` for error messages.
  If there is a line break before `body`, the message will be displayed on `=>` only,
  but the "full range" for the info view will still include `body`. -/
def withCaseRef [Monad m] [MonadRef m] (arrow body : Syntax) (x : m α) : m α :=
  withRef (mkNullNode #[arrow, body]) x

builtin_initialize registerTraceClass `Elab.tactic

end Lean.Elab.Tactic
