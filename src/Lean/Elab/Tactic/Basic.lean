/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Meta.Tactic.Util
import Lean.Elab.Term

namespace Lean.Elab
open Meta

/-- Assign `mvarId := sorry` -/
def admitGoal (mvarId : MVarId) : MetaM Unit :=
  mvarId.withContext do
    let mvarType ← inferType (mkMVar mvarId)
    mvarId.assign (← mkLabeledSorry mvarType (synthetic := true) (unique := true))

def goalsToMessageData (goals : List MVarId) : MessageData :=
  MessageData.joinSep (goals.map MessageData.ofGoal) m!"\n\n"

def Term.reportUnsolvedGoals (goals : List MVarId) : MetaM Unit := do
  logError <| MessageData.tagged `Tactic.unsolvedGoals <| m!"unsolved goals\n{goalsToMessageData goals}"
  goals.forM fun mvarId => admitGoal mvarId

namespace Tactic

structure Context where
  /-- Declaration name of the executing elaborator, used by `mkTacticInfo` to persist it in the info tree -/
  elaborator : Name
  /--
    If `true`, enable "error recovery" in some tactics. For example, `cases` tactic
    admits unsolved alternatives when `recover == true`. The combinator `withoutRecover <tac>` disables
    "error recovery" while executing `<tac>`. This is useful for tactics such as `first | ... | ...`.
  -/
  recover    : Bool := true

abbrev TacticM := ReaderT Context $ StateRefT State TermElabM
abbrev Tactic  := Syntax → TacticM Unit

/-
Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
whole monad stack at every use site. May eventually be covered by `deriving`.

See comment at `Monad TermElabM`
-/
@[always_inline]
instance : Monad TacticM :=
  let i := inferInstanceAs (Monad TacticM);
  { pure := i.pure, bind := i.bind }

instance : Inhabited (TacticM α) where
  default := fun _ _ => default

/-- Returns the list of goals. Goals may or may not already be assigned. -/
def getGoals : TacticM (List MVarId) :=
  return (← get).goals

def setGoals (mvarIds : List MVarId) : TacticM Unit :=
  modify fun _ => { goals := mvarIds }

def pruneSolvedGoals : TacticM Unit := do
  let gs ← getGoals
  let gs ← gs.filterM fun g => not <$> g.isAssigned
  setGoals gs

def getUnsolvedGoals : TacticM (List MVarId) := do
  pruneSolvedGoals
  getGoals

@[inline] private def TacticM.runCore (x : TacticM α) (ctx : Context) (s : State) : TermElabM (α × State) :=
  x ctx |>.run s

@[inline] private def TacticM.runCore' (x : TacticM α) (ctx : Context) (s : State) : TermElabM α :=
  Prod.fst <$> x.runCore ctx s

def run (mvarId : MVarId) (x : TacticM Unit) : TermElabM (List MVarId) :=
  mvarId.withContext do
   let pendingMVarsSaved := (← get).pendingMVars
   modify fun s => { s with pendingMVars := [] }
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
     aux.runCore' { elaborator := .anonymous } { goals := [mvarId] }
   finally
     modify fun s => { s with pendingMVars := pendingMVarsSaved }

protected def saveState : TacticM SavedState :=
  return { term := (← Term.saveState), tactic := (← get) }

def SavedState.restore (b : SavedState) (restoreInfo := false) : TacticM Unit := do
  b.term.restore restoreInfo
  set b.tactic

@[specialize, inherit_doc Term.withRestoreOrSaveFull]
def withRestoreOrSaveFull (reusableResult? : Option (α × SavedState))
    (tacSnap? : Option (Language.SnapshotBundle Tactic.TacticParsedSnapshot)) (act : TacticM α) :
    TacticM (α × SavedState) := do
  if let some (_, state) := reusableResult? then
    set state.tactic
  let reusableResult? := reusableResult?.map (fun (val, state) => (val, state.term))
  let (a, term) ← controlAt TermElabM fun runInBase => do
    Term.withRestoreOrSaveFull reusableResult? tacSnap? <| runInBase act
  return (a, { term, tactic := (← get) })

protected def getCurrMacroScope : TacticM MacroScope := do pure (← readThe Core.Context).currMacroScope
protected def getMainModule     : TacticM Name       := do pure (← getEnv).mainModule

unsafe def mkTacticAttribute : IO (KeyedDeclsAttribute Tactic) :=
  mkElabAttribute Tactic `builtin_tactic `tactic `Lean.Parser.Tactic `Lean.Elab.Tactic.Tactic "tactic" `Lean.Elab.Tactic.tacticElabAttribute

@[builtin_init mkTacticAttribute] opaque tacticElabAttribute : KeyedDeclsAttribute Tactic

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

/-!
Important: we must define `evalTactic` before we define
the instance `MonadExcept` for `TacticM` since it backtracks the state including error messages,
and this is bad when rethrowing the exception at the `catch` block in these methods.
We marked these places with a `(*)` in these methods.
-/

/--
  Auxiliary datastructure for capturing exceptions at `evalTactic`.
-/
structure EvalTacticFailure where
  exception : Exception
  state : SavedState

partial def evalTactic (stx : Syntax) : TacticM Unit := do
  profileitM Exception "tactic execution" (decl := stx.getKind) (← getOptions) <|
  withRef stx <| withIncRecDepth <| withFreshMacroScope <| match stx with
    | .node _ k _    =>
      if k == nullKind then
        -- Macro writers create a sequence of tactics `t₁ ... tₙ` using `mkNullNode #[t₁, ..., tₙ]`
        -- We could support incrementality here by allocating `n` new snapshot bundles but the
        -- practical value is not clear
        -- NOTE: `withTacticInfoContext` is used to preserve the invariant of `elabTactic` producing
        -- exactly one info tree, which is necessary for using `getInfoTreeWithContext`.
        Term.withoutTacticIncrementality true <| withTacticInfoContext stx do
          stx.getArgs.forM evalTactic
      else withTraceNode `Elab.step (fun _ => return stx) (tag := stx.getKind.toString) do
        let evalFns := tacticElabAttribute.getEntries (← getEnv) stx.getKind
        let macros  := macroAttribute.getEntries (← getEnv) stx.getKind
        if evalFns.isEmpty && macros.isEmpty then
          throwErrorAt stx "tactic '{stx.getKind}' has not been implemented"
        let s ← Tactic.saveState
        expandEval s macros evalFns #[]
    | .missing => pure ()
    | _ => throwError m!"unexpected tactic{indentD stx}"
where
    throwExs (failures : Array EvalTacticFailure) : TacticM Unit := do
     if h : 0 < failures.size  then
       -- For macros we want to report the error from the first registered / last tried rule (#3770)
       let fail := failures[failures.size - 1]
       fail.state.restore (restoreInfo := true)
       throw fail.exception -- (*)
     else
       throwErrorAt stx "unexpected syntax {indentD stx}"

    @[inline] handleEx (s : SavedState) (failures : Array EvalTacticFailure) (ex : Exception) (k : Array EvalTacticFailure → TacticM Unit) := do
      match ex with
      | .error .. =>
        trace[Elab.tactic.backtrack] ex.toMessageData
        let failures := failures.push ⟨ex, ← Tactic.saveState⟩
        s.restore (restoreInfo := true); k failures
      | .internal id _ =>
        if id == unsupportedSyntaxExceptionId then
          -- We do not store `unsupportedSyntaxExceptionId`, see throwExs
          s.restore (restoreInfo := true); k failures
        else if id == abortTacticExceptionId then
          for msg in (← Core.getMessageLog).toList do
            trace[Elab.tactic.backtrack] msg.data
          let failures := failures.push ⟨ex, ← Tactic.saveState⟩
          s.restore (restoreInfo := true); k failures
        else
          throw ex -- (*)

    expandEval (s : SavedState) (macros : List _) (evalFns : List _) (failures : Array EvalTacticFailure) : TacticM Unit :=
      match macros with
      | [] => eval s evalFns failures
      | m :: ms =>
        try
          withReader ({ · with elaborator := m.declName }) do
            withTacticInfoContext stx do
              let stx' ← adaptMacro m.value stx
              -- Support incrementality; see also Note [Incremental Macros]
              if evalFns.isEmpty && ms.isEmpty then  -- Only try incrementality in one branch
                if let some snap := (← readThe Term.Context).tacSnap? then
                  let nextMacroScope := (← getThe Core.State).nextMacroScope
                  let traceState ← getTraceState
                  let old? := do
                    let old ← snap.old?
                    -- If the kind is equal, we can assume the old version was a macro as well
                    guard <| old.stx.isOfKind stx.getKind
                    let state ← old.val.get.finished.get.state?
                    guard <| state.term.meta.core.nextMacroScope == nextMacroScope
                    -- check absence of traces; see Note [Incremental Macros]
                    guard <| state.term.meta.core.traceState.traces.size == 0
                    guard <| traceState.traces.size == 0
                    return old.val.get
                  if snap.old?.isSome && old?.isNone then
                    snap.old?.forM (·.val.cancelRec)
                  let promise ← IO.Promise.new
                  -- Store new unfolding in the snapshot tree
                  snap.new.resolve {
                    stx := stx'
                    diagnostics := .empty
                    inner? := none
                    finished := .finished stx' {
                      diagnostics := .empty
                      state? := (← Tactic.saveState)
                      moreSnaps := #[]
                    }
                    next := #[{ stx? := stx', task := promise.resultD default }]
                  }
                  -- Update `tacSnap?` to old unfolding
                  withTheReader Term.Context ({ · with tacSnap? := some {
                    new := promise
                    old? := do
                      let old ← old?
                      return ⟨old.stx, (← old.next[0]?)⟩
                  } }) do
                    evalTactic stx'
                  return
              evalTactic stx'
        catch ex => handleEx s failures ex (expandEval s ms evalFns)

    eval (s : SavedState) (evalFns : List _) (failures : Array EvalTacticFailure) : TacticM Unit := do
      match evalFns with
      | []              => throwExs failures
      | evalFn::evalFns => do
        try
          -- prevent unsupported tactics from accidentally accessing `Term.Context.tacSnap?`
          Term.withoutTacticIncrementality (!(← isIncrementalElab evalFn.declName)) do
          withReader ({ · with elaborator := evalFn.declName }) do
          withTacticInfoContext stx do
            evalFn.value stx
        catch ex => handleEx s failures ex (eval s evalFns)

def throwNoGoalsToBeSolved : TacticM α :=
  throwError "no goals to be solved"

def done : TacticM Unit := do
  let gs ← getUnsolvedGoals
  unless gs.isEmpty do
    Term.reportUnsolvedGoals gs
    throwAbortTactic

/--
Runs `x` with only the first unsolved goal as the goal.
Fails if there are no goal to be solved.
-/
def focus (x : TacticM α) : TacticM α := do
  let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved
  setGoals [mvarId]
  let a ← x
  let mvarIds' ← getUnsolvedGoals
  setGoals (mvarIds' ++ mvarIds)
  pure a

/--
Runs `tactic` with only the first unsolved goal as the goal, and expects it leave no goals.
Fails if there are no goal to be solved.
-/
def focusAndDone (tactic : TacticM α) : TacticM α :=
  focus do
    let a ← tactic
    done
    pure a

/-- Close the main goal using the given tactic. If it fails, log the error and `admit` -/
def closeUsingOrAdmit (tac : TacticM Unit) : TacticM Unit := do
  /- Important: we must define `closeUsingOrAdmit` before we define
     the instance `MonadExcept` for `TacticM` since it backtracks the state including error messages. -/
  let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved
  tryCatchRuntimeEx
    (focusAndDone tac)
    fun ex => do
      if (← read).recover then
        logException ex
        admitGoal mvarId
        setGoals mvarIds
      else
        throw ex

instance : MonadBacktrack SavedState TacticM where
  saveState := Tactic.saveState
  restoreState b := b.restore

/--
Non-backtracking `try`/`catch`.
-/
@[inline] protected def tryCatch {α} (x : TacticM α) (h : Exception → TacticM α) : TacticM α := do
  try x catch ex => h ex

/--
Backtracking `try`/`catch`. This is used for the `MonadExcept` instance for `TacticM`.
-/
@[inline] protected def tryCatchRestore {α} (x : TacticM α) (h : Exception → TacticM α) : TacticM α := do
  let b ← saveState
  try x catch ex => b.restore; h ex

instance : MonadExcept Exception TacticM where
  throw    := throw
  tryCatch := Tactic.tryCatchRestore

/-- Execute `x` with error recovery disabled -/
def withoutRecover (x : TacticM α) : TacticM α :=
  withReader (fun ctx => { ctx with recover := false }) x

@[inline] protected def orElse (x : TacticM α) (y : Unit → TacticM α) : TacticM α := do
  try withoutRecover x catch _ => y ()

instance : OrElse (TacticM α) where
  orElse := Tactic.orElse

instance : Alternative TacticM where
  failure := fun {_} => throwError "failed"
  orElse  := Tactic.orElse

/--
  Save the current tactic state for a token `stx`.
  This method is a no-op if `stx` has no position information.
  We use this method to save the tactic state at punctuation such as `;`
-/
def saveTacticInfoForToken (stx : Syntax) : TacticM Unit := do
  unless stx.getPos?.isNone do
    withTacticInfoContext stx (pure ())

/-- Elaborate `x` with `stx` on the macro stack -/
@[inline]
def withMacroExpansion (beforeStx afterStx : Syntax) (x : TacticM α) : TacticM α :=
  withMacroExpansionInfo beforeStx afterStx do
    withTheReader Term.Context (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

/-- Adapt a syntax transformation to a regular tactic evaluator. -/
def adaptExpander (exp : Syntax → TacticM Syntax) : Tactic := fun stx => do
  let stx' ← exp stx
  withMacroExpansion stx stx' $ evalTactic stx'

/-- Add the given goal to the front of the current list of goals. -/
def pushGoal (mvarId : MVarId) : TacticM Unit :=
  modify fun s => { s with goals := mvarId :: s.goals }

/-- Add the given goals to the front of the current list of goals. -/
def pushGoals (mvarIds : List MVarId) : TacticM Unit :=
  modify fun s => { s with goals := mvarIds ++ s.goals }

/-- Add the given goals at the end of the current list of goals. -/
def appendGoals (mvarIds : List MVarId) : TacticM Unit :=
  modify fun s => { s with goals := s.goals ++ mvarIds }

/--
Discard the first goal and replace it by the given list of goals,
keeping the other goals. This is used in conjunction with `getMainGoal`.

Contract: between `getMainGoal` and `replaceMainGoal`, nothing manipulates the goal list.

See also `Lean.Elab.Tactic.popMainGoal` and `Lean.Elab.Tactic.pushGoal`/`Lean.Elab.Tactic.pushGoal` for another interface.
-/
def replaceMainGoal (mvarIds : List MVarId) : TacticM Unit := do
  let (_ :: mvarIds') ← getGoals | throwNoGoalsToBeSolved
  modify fun _ => { goals := mvarIds ++ mvarIds' }

/-- Return the first goal. -/
def getMainGoal : TacticM MVarId := do
  loop (← getGoals)
where
  loop : List MVarId → TacticM MVarId
    | [] => throwNoGoalsToBeSolved
    | mvarId :: mvarIds => do
      if (← mvarId.isAssigned) then
        loop mvarIds
      else
        setGoals (mvarId :: mvarIds)
        return mvarId

/--
Return the first goal, and remove it from the goal list.

See also: `Lean.Elab.Tactic.pushGoal` and `Lean.Elab.Tactic.pushGoals`.
-/
def popMainGoal : TacticM MVarId := do
  let mvarId ← getMainGoal
  replaceMainGoal []
  return mvarId

/-- Return the main goal metavariable declaration. -/
def getMainDecl : TacticM MetavarDecl := do
  (← getMainGoal).getDecl

/-- Return the main goal tag. -/
def getMainTag : TacticM Name :=
  return (← getMainDecl).userName

/-- Return expected type for the main goal. -/
def getMainTarget : TacticM Expr := do
  instantiateMVars (← getMainDecl).type

/-- Execute `x` using the main goal local context and instances -/
def withMainContext (x : TacticM α) : TacticM α := do
  (← getMainGoal).withContext x

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

/--
Like `evalTacticAt`, but without restoring the goal list or pruning solved goals.
Useful when these tasks are already being done in an outer loop.
-/
def evalTacticAtRaw (tac : Syntax) (mvarId : MVarId) : TacticM (List MVarId) := do
  setGoals [mvarId]
  evalTactic tac
  getGoals

def ensureHasNoMVars (e : Expr) : TacticM Unit := do
  let e ← instantiateMVars e
  let pendingMVars ← getMVars e
  discard <| Term.logUnassignedUsingErrorInfos pendingMVars
  if e.hasExprMVar then
    throwError "tactic failed, resulting expression contains metavariables{indentExpr e}"

/--
Closes main goal using the given expression.
If `checkUnassigned == true`, then `val` must not contain unassigned metavariables.
Returns `true` if `val` was successfully used to close the goal.
-/
def closeMainGoal (tacName : Name) (val : Expr) (checkUnassigned := true): TacticM Unit := do
  if checkUnassigned then
    ensureHasNoMVars val
  let mvarId ← getMainGoal
  if (← mvarId.checkedAssign val) then
    replaceMainGoal []
  else
    throwTacticEx tacName mvarId m!"attempting to close the goal using{indentExpr val}\nthis is often due occurs-check failure"

@[inline] def liftMetaMAtMain (x : MVarId → MetaM α) : TacticM α := do
  withMainContext do x (← getMainGoal)

@[inline] def liftMetaTacticAux (tac : MVarId → MetaM (α × List MVarId)) : TacticM α := do
  withMainContext do
    let (a, mvarIds) ← tac (← getMainGoal)
    replaceMainGoal mvarIds
    pure a

/-- Get the mvarid of the main goal, run the given `tactic`,
then set the new goals to be the resulting goal list.-/
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

/-- Analogue of `liftMetaTactic` for tactics that do not return any goals. -/
@[inline] def liftMetaFinishingTactic (tac : MVarId → MetaM Unit) : TacticM Unit :=
  liftMetaTactic fun g => do tac g; pure []

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
  modifyMCtx fun mctx => Id.run do
    let mut mctx := mctx
    let mut idx  := 1
    for g in newGoals do
      if mctx.isAnonymousMVar g then
        if numAnonymous == 1 then
          mctx := mctx.setMVarUserName g parentTag
        else
          mctx := mctx.setMVarUserName g (parentTag ++ newSuffix.appendIndexAfter idx)
        idx := idx + 1
    pure mctx

/- Recall that `ident' := ident <|> Term.hole` -/
def getNameOfIdent' (id : Syntax) : Name :=
  if id.isIdent then id.getId else `_

/--
  Use position of `=> $body` for error messages.
  If there is a line break before `body`, the message will be displayed on `=>` only,
  but the "full range" for the info view will still include `body`. -/
def withCaseRef [Monad m] [MonadRef m] (arrow body : Syntax) (x : m α) : m α :=
  withRef (mkNullNode #[arrow, body]) x

builtin_initialize registerTraceClass `Elab.tactic
builtin_initialize registerTraceClass `Elab.tactic.backtrack

end Lean.Elab.Tactic
