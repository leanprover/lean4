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

abbrev TGrind := TSyntax `grind
abbrev TGrindStep := TSyntax ``Parser.Tactic.Grind.grindStep

/-- Result type for a `grind` Action -/
inductive ActionResult where
  | /--
    The goal has been closed, and you can use `seq` to close the goal efficiently.
    -/
    closed (seq : List TGrind)
  | /--
    The action could not make further progress.
    `gs` are subgoals that could not be closed. They are used for producing error messages.
    -/
    stuck (gs : List Goal)

def ActionResult.toMessageData : ActionResult → MessageData
  | .closed seq => m!"closed {seq}"
  | .stuck goals => m!"stuck {goals.map (·.mvarId)}"

instance : ToMessageData ActionResult where
  toMessageData := ActionResult.toMessageData

abbrev ActionCont : Type :=
  Goal → GrindM ActionResult

abbrev Action : Type :=
  Goal → (kna : ActionCont) → (kp : ActionCont) → GrindM ActionResult

namespace Action

def skip : Action := fun goal _ kp =>
  kp goal

def notApplicable : Action := fun goal kna _ =>
  kna goal

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
  match n with
  | 0 => kp goal
  | n+1 => x goal kp (fun goal' => loop n x goal' kp kp)

/--
Runs action `a` on the given `goal`.
-/
def run (goal : Goal) (a : Action) : GrindM ActionResult := do
  let k := fun goal => if goal.inconsistent then return .closed [] else return .stuck [goal]
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
next =>
  t₁
  ...
  tₙ
```
If the list is empty, it returns `next => done`.
-/
def mkGrindNext (s : List TGrind) : CoreM TGrind := do
  let s ← if s == [] then pure [← `(grind| done)] else pure s
  let s := mkGrindSeq s
  `(grind| next => $s:grindSeq)

/--
If tracing is enabled and continuation produced `.closed [t₁, ..., tₙ]`,
returns the singleton sequence `[t]` where `t` is
```
next =>
  t₁
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
If tracing is enabled and continuation produced `.closed [(next => t₁; ...; tₙ)]`,
returns `.close [t₁, ... tₙ]`
-/
def ungroup : Action := fun goal _ kp => do
  let r ← kp goal
  if (← getConfig).trace then
    match r with
    | .closed [tac] =>
      match tac with
      | `(grind| next => $seq;*) => return .closed <| seq.getElems.toList.map TGrindStep.getTactic
      | _ => return r
    | _ => return r
  else
    return r

/--
Appends a new tactic syntax to a successful result.
Used by leaf actions to record the tactic that produced progress.
If `(← getConfig).trace` is `false`, it just returns `r`.
-/
def concatTactic (r : ActionResult) (mk : GrindM (TSyntax `grind)) : GrindM ActionResult := do
  if (← getConfig).trace then
    match r with
    | .closed seq =>
      let tac ← mk
      return .closed (tac :: seq)
    | r => return r
  else
    return r

/-- Returns `.closed [← mk]` if tracing is enabled, and `.closed []` otherwise. -/
def closeWith (mk : GrindM (TSyntax `grind)) : GrindM ActionResult := do
  if (← getConfig).trace then
    return .closed [(← mk)]
  else
    return .closed []

/--
A terminal action which closes the goal or not.
This kind of action may make progress, but we only include `mkTac` into the resulting tactic sequence
if it closed the goal.
-/
public def terminalAction (check : GoalM Bool) (mkTac : GrindM (TSyntax `grind)) : Action := fun goal kna kp => do
  let (progress, goal') ← GoalM.run goal check
  if progress then
    if goal'.inconsistent then
      closeWith mkTac
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

example : notApplicable.loop n = skip := by
  funext; cases n <;> simp [loop]

example (a : Action) : a.loop 0 = skip := by
  funext; simp [loop]

theorem loop_skipIfNA (a : Action) : (a.loop n).skipIfNA = a.loop n := by
  funext; cases n <;> simp [loop]

example : skip.loop n = skip := by
  induction n
  next => funext; simp [loop]
  next ih =>
    rw [← loop_skipIfNA] at ih
    rw [← loop_skipIfNA]
    funext goal kna kp; simp [loop]
    replace ih := congrFun (congrFun (congrFun ih goal) kp) kp
    simp at ih
    assumption

example (a : Action) : a.loop (n+1) = (a >> a.loop n).skipIfNA := by
  funext goal kna kp; simp [loop]
end

end Action
end Lean.Meta.Grind
