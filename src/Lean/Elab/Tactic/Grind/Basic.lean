/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.Tactic.Grind.Main
import Lean.CoreM
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.PP
public section
namespace Lean.Elab.Tactic.Grind
open Meta

structure Context extends Tactic.Context where
  ctx     : Meta.Grind.Context
  methods : Grind.Methods
  params  : Grind.Params

open Meta.Grind (Goal)

structure State where
  symState   : Meta.Sym.State
  grindState : Meta.Grind.State
  goals      : List Goal

structure SavedState where
  term   : Term.SavedState
  tactic : State

abbrev GrindTacticM := ReaderT Context $ StateRefT State TermElabM

abbrev GrindTactic  := Syntax → GrindTacticM Unit

/-- Returns the list of goals. Goals may or may not already be assigned. -/
def getGoals : GrindTacticM (List Goal) :=
  return (← get).goals

def setGoals (goals : List Goal) : GrindTacticM Unit :=
  modify fun s => { s with goals }

def pruneSolvedGoals : GrindTacticM Unit := do
  let gs ← getGoals
  let gs := gs.filter fun g => !g.inconsistent
  setGoals gs

def getUnsolvedGoals : GrindTacticM (List Goal) := do
  pruneSolvedGoals
  getGoals

def getUnsolvedGoalMVarIds : GrindTacticM (List MVarId) := do
  pruneSolvedGoals
  let goals ← getGoals
  return goals.map (·.mvarId)

protected def saveState : GrindTacticM SavedState :=
  return { term := (← Term.saveState), tactic := (← get) }

def SavedState.restore (b : SavedState) (restoreInfo := false) : GrindTacticM Unit := do
  b.term.restore restoreInfo
  set b.tactic

@[always_inline]
instance : Monad GrindTacticM :=
  let i := inferInstanceAs (Monad GrindTacticM)
  { pure := i.pure, bind := i.bind }

instance : Inhabited (GrindTacticM α) where
  default := fun _ _ => default

unsafe builtin_initialize grindTacElabAttribute : KeyedDeclsAttribute GrindTactic ←
  mkElabAttribute GrindTactic `builtin_grind_tactic `grind_tactic
    `Lean.Parser.Tactic.Grind `Lean.Elab.Tactic.Grind.GrindTactic "grind"

def mkTacticInfo (mctxBefore : MetavarContext) (goalsBefore : List MVarId) (stx : Syntax) : GrindTacticM Info :=
  return Info.ofTacticInfo {
    elaborator    := (← read).elaborator
    mctxBefore    := mctxBefore
    goalsBefore   := goalsBefore
    stx           := stx
    mctxAfter     := (← getMCtx)
    goalsAfter    := (← getUnsolvedGoalMVarIds)
  }

def mkInitialTacticInfo (stx : Syntax) : GrindTacticM (GrindTacticM Info) := do
  let mctxBefore  ← getMCtx
  let goalsBefore ← getUnsolvedGoalMVarIds
  return mkTacticInfo mctxBefore goalsBefore stx

@[inline] def withTacticInfoContext (stx : Syntax) (x : GrindTacticM α) : GrindTacticM α := do
  withInfoContext x (← mkInitialTacticInfo stx)

structure EvalTacticFailure where
  exception : Exception
  state     : SavedState

partial def evalGrindTactic (stx : Syntax) : GrindTacticM Unit := do
  checkSystem "grind tactic execution"
  profileitM Exception "grind tactic execution" (decl := stx.getKind) (← getOptions) <|
  withRef stx <| withIncRecDepth <| withFreshMacroScope <| match stx with
    | .node _ k _    =>
      if k == nullKind then
        Term.withoutTacticIncrementality true <| withTacticInfoContext stx do
          stx.getArgs.forM evalGrindTactic
      else withTraceNode `Elab.step (fun _ => return stx) (tag := stx.getKind.toString) do
        let evalFns := grindTacElabAttribute.getEntries (← getEnv) stx.getKind
        let macros  := macroAttribute.getEntries (← getEnv) stx.getKind
        if evalFns.isEmpty && macros.isEmpty then
          throwErrorAt stx "Grind tactic `{stx.getKind}` has not been implemented"
        let s ← Grind.saveState
        expandEval s macros evalFns #[]
    | .missing => pure ()
    | _ => throwError m!"Unexpected grind tactic{indentD stx}"
where
    throwExs (failures : Array EvalTacticFailure) : GrindTacticM Unit := do
     if h : 0 < failures.size  then
       -- For macros we want to report the error from the first registered / last tried rule (#3770)
       let fail := failures[failures.size - 1]
       fail.state.restore (restoreInfo := true)
       throw fail.exception
     else
       throwErrorAt stx "Unexpected syntax{indentD stx}"

    @[inline] handleEx (s : SavedState) (failures : Array EvalTacticFailure) (ex : Exception) (k : Array EvalTacticFailure → GrindTacticM Unit) := do
      match ex with
      | .error .. =>
        trace[Elab.tactic.backtrack] ex.toMessageData
        let failures := failures.push ⟨ex, ← Grind.saveState⟩
        s.restore (restoreInfo := true); k failures
      | .internal id _ =>
        if id == unsupportedSyntaxExceptionId then
          -- We do not store `unsupportedSyntaxExceptionId`, see throwExs
          s.restore (restoreInfo := true); k failures
        else if id == abortTacticExceptionId then
          for msg in (← Core.getMessageLog).toList do
            trace[Elab.tactic.backtrack] msg.data
          let failures := failures.push ⟨ex, ← Grind.saveState⟩
          s.restore (restoreInfo := true); k failures
        else
          throw ex -- (*)

    expandEval (s : SavedState) (macros : List _) (evalFns : List _)
        (failures : Array EvalTacticFailure) : GrindTacticM Unit :=
      match macros with
      | [] => eval s evalFns failures
      | m :: ms =>
        try
          withReader ({ · with elaborator := m.declName }) do
            withTacticInfoContext stx do
              let stx' ← adaptMacro m.value stx
              evalGrindTactic stx'
        catch ex => handleEx s failures ex (expandEval s ms evalFns)

    eval (s : SavedState) (evalFns : List _) (failures : Array EvalTacticFailure) : GrindTacticM Unit := do
      match evalFns with
      | []              => throwExs failures
      | evalFn::evalFns => do
        try
          Term.withoutTacticIncrementality true do
          withReader ({ · with elaborator := evalFn.declName }) do
          withTacticInfoContext stx do
            evalFn.value stx
        catch ex => handleEx s failures ex (eval s evalFns)

def throwNoGoalsToBeSolved : GrindTacticM α :=
  throwError "No goals to be solved"

instance : MonadBacktrack SavedState GrindTacticM where
  saveState := Grind.saveState
  restoreState b := b.restore

/--
Runs `x` with only the first unsolved goal as the goal.
Fails if there are no goal to be solved.
-/
def focus (k : GrindTacticM α) : GrindTacticM α := do
  let goal :: goals ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  setGoals [goal]
  let a ← k
  let goals' ← getUnsolvedGoals
  setGoals (goals' ++ goals)
  pure a

/--
Non-backtracking `try`/`catch`.
-/
@[inline] protected def tryCatch {α} (x : GrindTacticM α) (h : Exception → GrindTacticM α) : GrindTacticM α := do
  try x catch ex => h ex

/--
Backtracking `try`/`catch`. This is used for the `MonadExcept` instance for `GrindTacticM`.
-/
@[inline] protected def tryCatchRestore {α} (x : GrindTacticM α) (h : Exception → GrindTacticM α)
    : GrindTacticM α := do
  let b ← saveState
  try x catch ex => b.restore; h ex

instance : MonadExcept Exception GrindTacticM where
  throw    := throw
  tryCatch := Grind.tryCatchRestore

/-- Execute `x` with error recovery disabled -/
def withoutRecover (x : GrindTacticM α) : GrindTacticM α :=
  withReader (fun ctx => { ctx with recover := false }) x

/--
Like `throwErrorAt`, but, if recovery is enabled, logs the error instead.
-/
def throwOrLogErrorAt (ref : Syntax) (msg : MessageData) : GrindTacticM Unit := do
  if (← read).recover then
    logErrorAt ref msg
  else
    throwErrorAt ref msg

/--
Like `throwError`, but, if recovery is enabled, logs the error instead.
-/
def throwOrLogError (msg : MessageData) : GrindTacticM Unit := do
  throwOrLogErrorAt (← getRef) msg

@[inline] protected def orElse (x : GrindTacticM α) (y : Unit → GrindTacticM α) : GrindTacticM α := do
  try withoutRecover x catch _ => y ()

instance : OrElse (GrindTacticM α) where
  orElse := Grind.orElse

instance : Alternative GrindTacticM where
  failure := fun {_} => throwError "Failed"
  orElse  := Grind.orElse

/--
Save the current tactic state for a token `stx`.
This method is a no-op if `stx` has no position information.
We use this method to save the tactic state at punctuation such as `;`
-/
def saveTacticInfoForToken (stx : Syntax) : GrindTacticM Unit := do
  unless stx.getPos?.isNone do
    withTacticInfoContext stx (pure ())

/-- Elaborate `x` with `stx` on the macro stack -/
@[inline]
def withMacroExpansion (beforeStx afterStx : Syntax) (x : GrindTacticM α) : GrindTacticM α :=
  withMacroExpansionInfo beforeStx afterStx do
    withTheReader Term.Context (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

/-- Adapt a syntax transformation to a regular tactic evaluator. -/
def adaptExpander (exp : Syntax → GrindTacticM Syntax) : GrindTactic := fun stx => do
  let stx' ← exp stx
  withMacroExpansion stx stx' <| evalGrindTactic stx'

/-- Return the first goal. -/
def getMainGoal : GrindTacticM Goal := do
  loop (← getGoals)
where
  loop : List Goal → GrindTacticM Goal
    | [] => throwNoGoalsToBeSolved
    | goal :: goals => do
      if goal.inconsistent then
        loop goals
      else
        setGoals (goal :: goals)
        return goal

/-- Execute `x` using the main goal local context and instances -/
def withMainContext (x : GrindTacticM α) : GrindTacticM α := do
  (← getMainGoal).mvarId.withContext x

def tryTactic? (tac : GrindTacticM α) : GrindTacticM (Option α) := do
  try
    pure (some (← tac))
  catch _ =>
    pure none

def tryTactic (tac : GrindTacticM α) : GrindTacticM Bool := do
  try
    discard tac
    pure true
  catch _ =>
    pure false

open Grind

/-
**Note**: Recall that `grind` uses the reducibility specified at `Config.reducible`
-/
def liftGrindM (k : GrindM α) : GrindTacticM α := do
  let ctx ← read
  let s ← get
  let ((a, grindState), symState) ← liftMetaM <| StateRefT'.run ((Grind.withGTransparency k) ctx.methods.toMethodsRef ctx.ctx |>.run s.grindState) s.symState
  modify fun s => { s with grindState, symState }
  return a

def replaceMainGoal (goals : List Goal) : GrindTacticM Unit := do
  let goals := goals.filter fun goal => !goal.inconsistent
  let (_ :: goals') ← getGoals | throwNoGoalsToBeSolved
  modify fun s => { s with goals := goals ++ goals' }

def liftGoalM (k : GoalM α) : GrindTacticM α := do
  let goal ← getMainGoal
  let (a, goal) ← liftGrindM <| k.run goal
  replaceMainGoal [goal]
  return a

def liftAction (a : Action) : GrindTacticM Unit := do
  let goal ← getMainGoal
  let ka := fun _ => throwError "tactic is not applicable"
  let kp := fun goal => return .stuck [goal]
  match (← liftGrindM <| a goal ka kp) with
  | .closed _ => replaceMainGoal []
  | .stuck gs => replaceMainGoal gs

def done : GrindTacticM Unit := do
  pruneSolvedGoals
  let goals ← getGoals
  unless goals.isEmpty do
    let params := (← read).params
    let results ← liftGrindM do goals.mapM fun goal => Grind.mkResult params (some goal)
    let msgs ← results.mapM fun result => result.toMessageData
    let msg := MessageData.joinSep msgs m!"\n\n"
    logError <| MessageData.tagged `Tactic.unsolvedGoals <| m!"unsolved goals\n{msg}"
    goals.forM fun goal => admitGoal goal.mvarId
    throwAbortTactic

/--
Runs `tactic` with only the first unsolved goal as the goal, and expects it leave no goals.
Fails if there are no goal to be solved.
-/
def focusAndDone (tactic : GrindTacticM α) : GrindTacticM α :=
  focus do
    let a ← tactic
    done
    pure a

/-- Close the main goal using the given tactic. If it fails, log the error and `admit` -/
def closeUsingOrAdmit (tac : GrindTacticM Unit) : GrindTacticM Unit := do
  /- Important: we must define `closeUsingOrAdmit` before we define
     the instance `MonadExcept` for `GrindTacticM` since it backtracks the state including error messages. -/
  let goal :: goals ← getUnsolvedGoals | throwNoGoalsToBeSolved
  tryCatchRuntimeEx
    (focusAndDone tac)
    fun ex => do
      if (← read).recover then
        logException ex
        admitGoal goal.mvarId
        setGoals goals
      else
        throw ex

def GrindTacticM.run (x : GrindTacticM α) (ctx : Context) (s : State) : TermElabM (α × State) :=
  x ctx |>.run s

def mkEvalTactic' (elaborator : Name) (params : Params) : TermElabM (Goal → TSyntax `grind → GrindM (List Goal)) := do
  let termState ← getThe Term.State
  let termCtx ← readThe Term.Context
  let eval (goal : Goal) (stx : TSyntax `grind) : GrindM (List Goal) := do
    let methods ← getMethods
    let grindCtx ← readThe Meta.Grind.Context
    let grindState ← get
    let symState ← getThe Sym.State
    -- **Note**: we discard changes to `Term.State`
    let (subgoals, grindState', symState') ← Term.TermElabM.run' (ctx := termCtx) (s := termState) do
      let (_, s) ← GrindTacticM.run
            (ctx := { recover := false, methods, ctx := grindCtx, params, elaborator })
            (s := { grindState, symState, goals := [goal] }) do
        evalGrindTactic stx.raw
        pruneSolvedGoals
      return (s.goals, s.grindState, s.symState)
    set grindState'
    set symState'
    return subgoals
  return eval

def mkEvalTactic (params : Params) : TacticM (Goal → TSyntax `grind → GrindM (List Goal)) := do
  mkEvalTactic' (← read).elaborator params

def GrindTacticM.runAtGoal (mvarId : MVarId) (params : Params) (k : GrindTacticM α) : TacticM (α × State) := do
  let evalTactic ← mkEvalTactic params
  /-
  **Note**: We don't want to close branches using `sorry` after applying `intros + assertAll`.
  Reconsider the option `useSorry`.
  -/
  let params' := { params with config.useSorry := false }
  let (methods, ctx, state) ← liftMetaM <| GrindM.runAtGoal mvarId params' (evalTactic? := some evalTactic) fun goal => do
      let a : Action := Action.intros 0 >> Action.assertAll
      let goals ← match (← a.run goal) with
        | .closed _ => pure []
        | .stuck gs => pure gs
      let methods ← getMethods
      let ctx ← readThe Meta.Grind.Context
      /- Restore original config -/
      let ctx := { ctx with config := params.config }
      let grindState ← get
      let symState ← getThe Sym.State
      return (methods, ctx, { grindState, symState, goals })
  let tctx ← read
  k { tctx with methods, ctx, params } |>.run state

end Lean.Elab.Tactic.Grind
