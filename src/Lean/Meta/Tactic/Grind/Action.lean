/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public section
namespace Lean.Meta.Grind
/-!
# `Action`

`Action` is the *control interface* for `grind`’s search steps. It is defined in
Continuation-Passing Style (CPS):
```
abbrev Action :=
  Goal → (kna : Goal → GrindM ActionResult) → (kp : Goal → GrindM ActionResult) → GrindM ActionResult
```
An Action receives: the current `Goal`, a continuation `kna` to run when the action is not applicable,
and a continuation `kp` to run when it makes progress.

It returns an `ActionResult`:
- `.closed seq`: the goal was fully solved, and `seq` is the sequence of tactics
that, if replayed, closes the goal.

- `.stuck gs`: search ran and got stuck at goals `gs`. Remark: actions such as `splitNext` can decide
  whether they stop at the first failure or not.

## Why CPS?

Two core requirements motivated CPS:

- Non-chronological backtracking (NCB) for branching steps like `splitNext`.
A branching action must be able to run the full continuation on each
subgoal and decide—based on the entire downstream proof whether the case split is
actually needed or not. CPS gives the action visibility and control over `kp`.

- Tactic script generation. Some leaves (e.g. `ematch`)
should log only the facts/instantiations actually used by the final proof.
Running the continuation first and then post-processing what happened lets an
action commit exactly the steps that mattered.

## Contract (what every `Action` must guarantee)

- Return exactly once. An action may call `kp` zero or more times internally
(e.g. once per branch), but it must eventually return a single `ActionResult`.

- `.stuck g` and `.closed seq` reflect the final choice the action made after
any internal calls to `kp`. Combinators reason only about this final result.

- When an action is not applicable, it must invoke `kna` and perform no
observable effects.

## Why `Action` is not a `Monad`

Although it looks like “a computation that can call a continuation”, `Action`
is a control operator, not a lawful monad:

- Multi-shot continuations. `splitNext` legitimately calls `kp` multiple times
(once per subgoal). Standard `bind` assumes a linear continuation. Duplicating
the continuation breaks associativity (agreed?)

- Future inspection. Many actions decide what to keep/commit after seeing
the entire result of `kp` (e.g., the generated proof term). That is delimited control
(`callCC`/`handlers`) rather than plain monadic sequencing. It seems overkill to
use `callCC` here.

-/

abbrev TGrindStep := TSyntax ``Parser.Tactic.Grind.grindStep

def ActionResult.toMessageData : ActionResult → MessageData
  | .closed seq => m!"closed {seq}"
  | .stuck goals => m!"stuck {goals.map (·.mvarId)}"

instance : ToMessageData ActionResult where
  toMessageData := ActionResult.toMessageData

namespace Action

def skip : Action := fun goal _ kp =>
  kp goal

/--
If the `goal` is already inconsistent, returns `.closed []`. Otherwise, executes
then not applicable continuation.
-/
def done : Action := fun goal kna _ => do
  if goal.inconsistent then
    return .closed []
  else
    kna goal

/--
`x >> y`, executes `x` and then `y`
- If `x` is not applicable, then `x >> y` is not applicable.
- If `y` is not applicable, it behaves like a skip.
-/
def andThen (x y : Action) : Action := fun goal kna kp =>
  x goal kna fun goal' => y goal' kp kp

instance : AndThen Action where andThen x y := Action.andThen x (y ())

/--
Choice: tries `x`, if not applicable, tries `y`.
-/
protected def orElse (x y : Action) : Action := fun goal kna kp => do
  x goal (fun goal => y goal kna kp) kp

instance : OrElse Action where
  orElse x y := Action.orElse x (y ())

/--
Repeats `x` up to `n` times while it remains applicable.
-/
def loop (n : Nat) (x : Action) : Action := fun goal _ kp =>
  tryCatchRuntimeEx
    (match n with
     | 0 => kp goal
     | n+1 => x goal kp (fun goal' => loop n x goal' kp kp))
    (fun ex => do
      if ex.isMaxHeartbeat || ex.isMaxRecDepth then
        reportIssue! ex.toMessageData
        return .stuck [goal]
      else
        throw ex)

/-- `loop` reference implementation without `tryCatchRuntimeEx` for proving sanity checking lemmas. -/
def loopRef (n : Nat) (x : Action) : Action := fun goal _ kp =>
  match n with
  | 0 => kp goal
  | n+1 => x goal kp (fun goal' => loopRef n x goal' kp kp)


/--
Runs action `a` on the given `goal`.
-/
def run (goal : Goal) (a : Action) : GrindM ActionResult := do
  let k := fun goal => do
    if goal.inconsistent then
      return .closed []
    else if (← getConfig).trace && (← getConfig).useSorry then
      goal.mvarId.admit
      let sorryTac ← `(grind| sorry)
      return .closed [sorryTac]
    else
      return .stuck [goal]
  a goal k k

/--
Executes `x`, but behaves like a `skip` if it is not applicable.
-/
def skipIfNA (x : Action) : Action := fun goal _ kp =>
  x goal kp kp

/-- ``TSyntax `grind`` => ``TSyntax `Lean.Parser.Tactic.Grind.grindStep`` -/
def mkGrindStep (t : TGrind) : TGrindStep :=
  mkNode ``Parser.Tactic.Grind.grindStep #[ t, mkNullNode ]

def TGrindStep.getTactic : TGrindStep → TGrind
  | `(Parser.Tactic.Grind.grindStep| $tac:grind $[| $_]?) => tac
  | _ => ⟨mkNullNode⟩

def mkGrindSeq (s : List TGrind) : TSyntax ``Parser.Tactic.Grind.grindSeq :=
  let s := s.map fun tac => (mkGrindStep tac).raw
  let s := s.intersperse (mkNullNode #[])
  mkNode ``Parser.Tactic.Grind.grindSeq #[
  mkNode ``Parser.Tactic.Grind.grindSeq1Indented #[
  mkNullNode s.toArray
  ]]

/--
Given `[t₁, ..., tₙ]`, returns
```
· t₁
  ...
  tₙ
```
If the list is empty, it returns `· done`.
-/
def mkGrindNext (s : List TGrind) : CoreM TGrind := do
  let s ← if s == [] then pure [← `(grind| done)] else pure s
  let s := mkGrindSeq s
  `(grind| · $s:grindSeq)

/--
Given `[t₁, ..., tₙ]`, returns
```
(t₁
 ...
 tₙ)
```
If the list is empty, it returns `(skip)`.
-/
private def mkGrindParen (s : List TGrind) : CoreM TGrind := do
  let s ← if s == [] then pure [← `(grind| skip)] else pure s
  let s := mkGrindSeq s
  `(grind| ($s:grindSeq))

/--
If tracing is enabled and continuation produced `.closed [t₁, ..., tₙ]`,
returns the singleton sequence `[t]` where `t` is
```
· t₁
  ...
  tₙ
```
-/
def group : Action := fun goal _ kp => do
  let r ← kp goal
  if (← getConfig).trace then
    match r with
    | .closed seq => return .closed [← mkGrindNext seq]
    | _ => return r
  else
    return r

/--
If tracing is enabled and continuation produced `.closed [(next => t₁; ...; tₙ)]` or its variant using `·`
returns `.close [t₁, ... tₙ]`
-/
def ungroup : Action := fun goal _ kp => do
  let r ← kp goal
  if (← getConfig).trace then
    match r with
    | .closed [tac] =>
      match tac with
      | `(grind| next => $seq;*)
      | `(grind| · $seq;*) =>
        return .closed <| seq.getElems.toList.map TGrindStep.getTactic
      | _ => return r
    | _ => return r
  else
    return r

/--
Appends a new tactic syntax to a successful result.
Used by leaf actions to record the tactic that produced progress.
If `(← getConfig).trace` is `false`, it just returns `r`.
-/
def concatTactic (r : ActionResult) (mk : GrindM TGrind) : GrindM ActionResult := do
  if (← getConfig).trace then
    match r with
    | .closed seq =>
      let tac ← mk
      return .closed (tac :: seq)
    | r => return r
  else
    return r

/-- Returns `.closed [← mk]` if tracing is enabled, and `.closed []` otherwise. -/
def closeWith (mk : GrindM TGrind) : GrindM ActionResult := do
  if (← getConfig).trace then
    return .closed [(← mk)]
  else
    return .closed []

/--
A terminal action which closes the goal or not.
This kind of action may make progress, but we only include `mkTac` into the resulting tactic sequence
if it closed the goal.
-/
def terminalAction (check : GoalM Bool) (mkTac : GrindM TGrind) : Action := fun goal kna kp => do
  let (progress, goal') ← GoalM.run goal check
  if progress then
    if goal'.inconsistent then
      closeWith mkTac
    else
      kp goal'
  else
    kna goal'

def saveStateIfTracing : GrindM (Option SavedState) := do
  if (← getConfig).trace then
    return some (← saveState)
  else
    return none
/--
Returns `true` if the tactic sequence `seq` closes `goal` starting at saved state `s?`.
If `s?` is `none` just returns `true`.
-/
def checkSeqAt (s? : Option SavedState) (goal : Goal) (seq : List TGrind) : GrindM Bool := do
  let some s := s? | return true
  Lean.withoutModifyingState do
    s.restore
    let tac ← mkGrindParen seq
    -- **Note**: Ensure tracing is disabled.
    withTheReader Grind.Context (fun ctx => { ctx with config.trace := false }) do
      try
        let subgoals ← evalTactic goal tac
        return subgoals.isEmpty
      catch _  =>
        return false

/--
Helper action that checks whether the resulting tactic script produced by its continuation
can close the original goal.
If `warnOnly = true`, just generates a warning message instead of an error
-/
def checkTactic (warnOnly : Bool) : Action := fun goal _ kp => do
  let s ← saveStateIfTracing
  let r ← kp goal
  match r with
  | .closed seq =>
    unless (← checkSeqAt s goal seq) do
      let m := m!"generated tactic cannot close the goal{indentD (← mkGrindNext seq)}\nInitial goal\n{goal.mvarId}"
      if warnOnly then
        logWarning m
      else
        throwError m
    return r
  | _ => return r

/--
Helper action for satellite solvers that use `CheckResult`.
-/
def solverAction (check : GoalM CheckResult) (mkTac : GrindM TGrind) : Action := fun goal kna kp => do
  let saved? ← saveStateIfTracing
  let (result, goal') ← GoalM.run goal check
  match result with
  | .none       => kna goal'
  | .progress   => kp goal'
  | .propagated =>
    let goal' ← GoalM.run' goal' processNewFacts
    if goal'.inconsistent then
      closeWith mkTac
    else if (← getConfig).trace then
      match (← kp goal') with
      | .closed seq =>
        /-
        **Note**: Check whether the progress made by this solver was actually used to close the goal.
        This is not just an optimization, if we include an unnecessary step, we may fail to replay
        the generated script when `cases` steps are pruned using non-chronological backtracking (NCB).
        For example, when executing `finish?`, we may have performed a `cases #<anchor>` step
        that enabled `ring` to propagate a new fact. If this fact is not used in the final proof,
        and the corresponding `cases #<anchor>` step is pruned by NCB, the `ring` step will fail during replay.
        -/
        if (← checkSeqAt saved? goal seq) then
          return .closed seq
        else
          let tac ← mkTac
          return .closed (tac :: seq)
      | r => return r
    else
      kp goal'
  | .closed     => closeWith mkTac

def mbtc : Action := fun goal kna kp => do
  let saved? ← saveStateIfTracing
  let (progress, goal') ← GoalM.run goal Solvers.mbtc
  if progress then
    if (← getConfig).trace then
      match (← kp goal') with
      | .closed seq =>
        if (← checkSeqAt saved? goal seq) then
          return .closed seq
        else
          let tac ← `(grind| mbtc)
          return .closed (tac :: seq)
      | r => return r
    else
      kp goal'
  else
    kna goal'

section
/-!
Some sanity check properties.
-/
attribute [local simp] HAndThen.hAndThen AndThen.andThen Action.andThen
attribute [local simp] HOrElse.hOrElse OrElse.orElse Action.orElse
attribute [local simp] skip notApplicable skipIfNA

example (a : Action) : (a >> skip) = a := by
  funext; simp

example (a : Action) : (a >> notApplicable) = a := by
  funext; simp

example (a : Action) : (skip >> a) = a.skipIfNA := by
  funext; simp

example (a b : Action) : (a.skipIfNA >> b) = a.skipIfNA >> b.skipIfNA := by
  funext goal kna kp; simp

example (a : Action) : (notApplicable >> a) = notApplicable := by
  funext; simp

example (a : Action) : (notApplicable <|> a) = a := by
  funext; simp

example (a : Action) : (skip <|> a) = skip := by
  funext; simp

example (a b : Action) : (a.skipIfNA <|> b) = a.skipIfNA := by
  funext; simp

example : notApplicable.loopRef n = skip := by
  funext; cases n <;> simp [loopRef]

example (a : Action) : a.loopRef 0 = skip := by
  funext; simp [loopRef]

theorem loop_skipIfNA (a : Action) : (a.loopRef n).skipIfNA = a.loopRef n := by
  funext; cases n <;> simp [loopRef]

example : skip.loopRef n = skip := by
  induction n
  next => funext; simp [loopRef]
  next ih =>
    rw [← loop_skipIfNA] at ih
    rw [← loop_skipIfNA]
    funext goal kna kp; simp [loopRef]
    replace ih := congrFun (congrFun (congrFun ih goal) kp) kp
    simp at ih
    assumption

example (a : Action) : a.loopRef (n+1) = (a >> a.loopRef n).skipIfNA := by
  funext goal kna kp; simp [loopRef]
end

end Action
end Lean.Meta.Grind
