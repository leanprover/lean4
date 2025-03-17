/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, David Renshaw
-/
prelude
import Init.Data.Sum
import Lean.LabelAttribute
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Backtrack
import Lean.Meta.Tactic.Constructor
import Lean.Meta.Tactic.Repeat
import Lean.Meta.Tactic.Symm
import Lean.Elab.Term

/-!
# `solve_by_elim`, `apply_rules`, and `apply_assumption`.

`solve_by_elim` takes a collection of facts from the local context or
supplied as arguments by the user, and performs a backtracking
depth-first search by attempting to `apply` these facts to the goal.

It is a highly configurable tactic, with options to control the
backtracking, to solve multiple goals simultaneously (with backtracking
between goals), or to supply a discharging tactic for unprovable goals.

`apply_rules` and `apply_assumption` are much simpler tactics which do
not perform backtracking, but are currently implemented in terms of
`solve_by_elim` with backtracking disabled, in order to be able to share
the front-end customisation and parsing of user options. It would be
reasonable to further separate these in future.
-/

open Lean Meta Elab Tactic

namespace Lean.Meta.SolveByElim

initialize registerTraceClass `Meta.Tactic.solveByElim

/--
`applyTactics lemmas goal` will return an iterator that applies the
lemmas to the goal `goal` and returns ones that succeed.

Providing this to the `backtracking` tactic,
we can perform backtracking search based on applying a list of lemmas.

``applyTactics (trace := `name)`` will construct trace nodes for ``name` indicating which
calls to `apply` succeeded or failed.
-/
def applyTactics (cfg : ApplyConfig := {}) (transparency : TransparencyMode := .default)
    (lemmas : List Expr) (g : MVarId) : MetaM (Lean.Meta.Iterator (List Lean.MVarId)) := do
  pure <|
    (← Meta.Iterator.ofList lemmas).filterMapM (fun e => observing? do
      withTraceNode `Meta.Tactic.solveByElim (return m!"{exceptEmoji ·} trying to apply: {e}") do
        let goals ← withTransparency transparency (g.apply e cfg)
        -- When we call `apply` interactively, `Lean.Elab.Tactic.evalApplyLikeTactic`
        -- deals with closing new typeclass goals by calling
        -- `Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing`.
        -- It seems we can't reuse that machinery down here in `MetaM`,
        -- so we just settle for trying to close each subgoal using `inferInstance`.
        goals.filterM fun g => try g.inferInstance; pure false catch _ => pure true)

/--
`applyFirst lemmas goal` applies the first of the `lemmas`
which can be successfully applied to `goal`, and fails if none apply.

We use this in `apply_rules` and `apply_assumption` where backtracking is not needed.
-/
def applyFirst (cfg : ApplyConfig := {}) (transparency : TransparencyMode := .default)
    (lemmas : List Expr) (g : MVarId) : MetaM (List MVarId) := do
  (← applyTactics cfg transparency lemmas g).head

open Lean.Meta.Tactic.Backtrack (BacktrackConfig backtrack)

/-- The default `maxDepth` for `apply_rules` is higher. -/
structure ApplyRulesConfig extends BacktrackConfig, ApplyConfig where
  /-- Transparency mode for calls to `apply`. -/
  transparency : TransparencyMode := .default
  /-- Also use symmetric versions (via `@[symm]`) of local hypotheses. -/
  symm : Bool := true
  /-- Try proving the goal via `exfalso` if `solve_by_elim` otherwise fails.
  This is only used when operating on a single goal. -/
  exfalso : Bool := true
  maxDepth := 50

/--
Configuration structure to control the behaviour of `solve_by_elim`:
* transparency mode for calls to `apply`
* whether to use `symm` on hypotheses and `exfalso` on the goal as needed,
* see also `BacktrackConfig` for hooks allowing flow control.
-/
structure SolveByElimConfig extends ApplyRulesConfig where
  /-- Enable backtracking search. -/
  backtracking : Bool := true
  maxDepth := 6
  /-- Trying calling `intro` if no lemmas apply. -/
  intro : Bool := true
  /-- Try calling `constructor` if no lemmas apply. -/
  constructor : Bool := true

namespace SolveByElimConfig

instance : Coe SolveByElimConfig BacktrackConfig := ⟨(·.toApplyRulesConfig.toBacktrackConfig)⟩

/-- Create or modify a `Config` which allows a class of goals to be returned as subgoals. -/
def accept (cfg : SolveByElimConfig := {}) (test : MVarId → MetaM Bool) : SolveByElimConfig :=
  { cfg with
    discharge := fun g => do
      if (← test g) then
        pure none
      else
        cfg.discharge g }

/--
Create or modify a `Config` which runs a tactic on the main goal.
If that tactic fails, fall back to the `proc` behaviour of `cfg`.
-/
def mainGoalProc (cfg : SolveByElimConfig := {}) (proc : MVarId → MetaM (List MVarId)) : SolveByElimConfig :=
  { cfg with
    proc := fun orig goals => match goals with
    | [] => cfg.proc orig []
    | g :: gs => try
        return (← proc g) ++ gs
      catch _ => cfg.proc orig goals }

/-- Create or modify a `Config` which calls `intro` on each goal before applying lemmas. -/
-- Because `SolveByElim` works on each goal in sequence, even though
-- `mainGoalProc` only applies this operation on the main goal,
-- it is applied to every goal before lemmas are applied.
def intros (cfg : SolveByElimConfig := {}) : SolveByElimConfig :=
  cfg.mainGoalProc fun g => do pure [(← g.intro1P).2]

/-- Attempt typeclass inference on each goal, before applying lemmas. -/
-- Because `SolveByElim` works on each goal in sequence, even though
-- `mainGoalProc` only applies this operation on the main goal,
-- it is applied to every goal before lemmas are applied.
def synthInstance (cfg : SolveByElimConfig := {}) : SolveByElimConfig :=
  cfg.mainGoalProc fun g => do
    g.assign (← Lean.Meta.synthInstance (← g.getType))
    pure []

/-- Add a discharging tactic, falling back to the original discharging tactic if it fails.
Return `none` to return the goal as a new subgoal, or `some goals` to replace it. -/
def withDischarge (cfg : SolveByElimConfig := {}) (discharge : MVarId → MetaM (Option (List MVarId))) : SolveByElimConfig :=
  { cfg with
    discharge := fun g => try discharge g
      catch _ => cfg.discharge g }

/-- Create or modify a `SolveByElimConfig` which calls `intro` on any goal for which no lemma applies. -/
def introsAfter (cfg : SolveByElimConfig := {}) : SolveByElimConfig :=
  cfg.withDischarge fun g => do pure [(← g.intro1P).2]

/-- Call `constructor` when no lemmas apply. -/
def constructorAfter (cfg : SolveByElimConfig := {}) : SolveByElimConfig :=
  cfg.withDischarge fun g => g.constructor {newGoals := .all}

/-- Create or modify a `Config` which
calls `synthInstance` on any goal for which no lemma applies. -/
def synthInstanceAfter (cfg : SolveByElimConfig := {}) : SolveByElimConfig :=
  cfg.withDischarge fun g => do
    g.assign (← Lean.Meta.synthInstance (← g.getType))
    pure (some [])

/--
Create or modify a `Config` which rejects branches for which `test`,
applied to the instantiations of the original goals, fails or returns `false`.
-/
def testPartialSolutions (cfg : SolveByElimConfig := {}) (test : List Expr → MetaM Bool) : SolveByElimConfig :=
  { cfg with
    proc := fun orig goals => do
      guard <| ← test (← orig.mapM fun m => m.withContext do instantiateMVars (.mvar m))
      cfg.proc orig goals }

/--
Create or modify a `SolveByElimConfig` which rejects complete solutions for which `test`,
applied to the instantiations of the original goals, fails or returns `false`.
-/
def testSolutions (cfg : SolveByElimConfig := {}) (test : List Expr → MetaM Bool) : SolveByElimConfig :=
  cfg.testPartialSolutions fun sols => do
    if sols.any Expr.hasMVar then
      pure true
    else
      test sols

/--
Create or modify a `Config` which only accept solutions
for which every expression in `use` appears as a subexpression.
-/
def requireUsingAll (cfg : SolveByElimConfig := {}) (use : List Expr) : SolveByElimConfig :=
  cfg.testSolutions fun sols => do
    pure <| use.all fun e => sols.any fun s => e.occurs s

/--
Process the `intro` and `constructor` options by implementing the `discharger` tactic.
-/
def processOptions (cfg : SolveByElimConfig) : SolveByElimConfig :=
  let cfg := if cfg.intro then introsAfter { cfg with intro := false } else cfg
  let cfg := if cfg.constructor then constructorAfter { cfg with constructor := false } else cfg
  cfg

end SolveByElimConfig

/--
Elaborate a list of lemmas and local context.
See `mkAssumptionSet` for an explanation of why this is needed.
-/
def elabContextLemmas (cfg : SolveByElimConfig) (g : MVarId)
    (lemmas : List (TermElabM Expr)) (ctx : SolveByElimConfig → TermElabM (List Expr)) :
    MetaM (List Expr) := do
  g.withContext (Elab.Term.TermElabM.run' do pure ((← ctx cfg) ++ (← lemmas.mapM id)))

/-- Returns the list of tactics corresponding to applying the available lemmas to the goal. -/
def applyLemmas (cfg : SolveByElimConfig)
    (lemmas : List (TermElabM Expr)) (ctx : SolveByElimConfig → TermElabM (List Expr))
    (g : MVarId) : MetaM (Meta.Iterator (List MVarId)) := do
  let es ← elabContextLemmas cfg g lemmas ctx
  applyTactics cfg.toApplyConfig cfg.transparency es g

/-- Applies the first possible lemma to the goal. -/
def applyFirstLemma (cfg : SolveByElimConfig)
    (lemmas : List (TermElabM Expr)) (ctx : SolveByElimConfig → TermElabM (List Expr))
    (g : MVarId) : MetaM (List MVarId) := do
  let es ← elabContextLemmas cfg g lemmas ctx
  applyFirst cfg.toApplyConfig cfg.transparency es g

/--
Solve a collection of goals by repeatedly applying lemmas, backtracking as necessary.

Arguments:
* `cfg : SolveByElimConfig` additional configuration options
  (options for `apply`, maximum depth, and custom flow control)
* `lemmas : List (TermElabM Expr)` lemmas to apply.
  These are thunks in `TermElabM` to avoid stuck metavariables.
* `ctx : TermElabM (List Expr)` monadic function returning the local hypotheses to use.
* `goals : List MVarId` the initial list of goals for `solveByElim`

Returns a list of suspended goals, if it succeeded on all other subgoals.
By default `cfg.suspend` is `false,` `cfg.discharge` fails, and `cfg.failAtMaxDepth` is `true`,
and so the returned list is always empty.
Custom wrappers (e.g. `apply_assumption` and `apply_rules`) may modify this behaviour.
-/
def solveByElim (cfg : SolveByElimConfig)
    (lemmas : List (TermElabM Expr)) (ctx : SolveByElimConfig → TermElabM (List Expr))
    (goals : List MVarId) : MetaM (List MVarId) := do
  let cfg := cfg.processOptions
  try
    run cfg goals
  catch e => do
    -- Implementation note: as with `cfg.symm`, this is different from the mathlib3 approach,
    -- for (not as severe) performance reasons.
    match goals, cfg.exfalso with
    | [g], true =>
      withTraceNode `Meta.Tactic.solveByElim
          (fun _ => return m!"⏮️ starting over using `exfalso`") do
        run cfg [← g.exfalso]
    | _, _ => throw e
where
  /-- Run either backtracking search, or repeated application, on the list of goals. -/
  run (cfg : SolveByElimConfig) : List MVarId → MetaM (List MVarId) :=
    if cfg.backtracking then
      backtrack cfg `Meta.Tactic.solveByElim (applyLemmas cfg lemmas ctx)
    else
      Lean.Meta.repeat1' (maxIters := cfg.maxDepth) (applyFirstLemma cfg lemmas ctx)

/--
If `symm` is `true`, then adds in symmetric versions of each hypothesis.
-/
def saturateSymm (symm : Bool) (hyps : List Expr) : MetaM (List Expr) := do
  if symm then
    let extraHyps ← hyps.filterMapM fun hyp => try some <$> hyp.applySymm catch _ => pure none
    return hyps ++ extraHyps
  else
    return hyps

/--
A `MetaM` analogue of the `apply_rules` user tactic.

We pass the lemmas as `TermElabM Expr` rather than just `Expr`,
so they can be generated fresh for each application, to avoid stuck metavariables.

By default it uses all local hypotheses, but you can disable this with `only := true`.
If you need to remove particular local hypotheses, call `solveByElim` directly.
-/
def _root_.Lean.MVarId.applyRules (cfg : SolveByElimConfig) (lemmas : List (TermElabM Expr))
    (only : Bool := false) (g : MVarId) : MetaM (List MVarId) := do
  let ctx (cfg : SolveByElimConfig) : TermElabM (List Expr) :=
    if only then pure []
    else do saturateSymm cfg.symm (← getLocalHyps).toList
  solveByElim { cfg with backtracking := false } lemmas ctx [g]

open Lean.Parser.Tactic

/--
`mkAssumptionSet` builds a collection of lemmas for use in
the backtracking search in `solve_by_elim`.

* By default, it includes all local hypotheses, along with `rfl`, `trivial`, `congrFun`
  and `congrArg`.
* The flag `noDefaults` removes these.
* The flag `star` includes all local hypotheses, but not `rfl`, `trivial`, `congrFun`,
  or `congrArg`. (It doesn't make sense to use `star` without `noDefaults`.)
* The argument `add` is the list of terms inside the square brackets that did not have `-`
  and can be used to add expressions or local hypotheses
* The argument `remove` is the list of terms inside the square brackets that had a `-`,
  and can be used to remove local hypotheses.
  (It doesn't make sense to remove expressions which are not local hypotheses,
  to remove local hypotheses unless `!noDefaults || star`,
  and it does not make sense to use `star` unless you remove at least one local hypothesis.)

`mkAssumptionSet` returns not a `List expr`, but a `List (TermElabM Expr) × TermElabM (List Expr)`.
There are two separate problems that need to be solved.

### Stuck metavariables

Lemmas with implicit arguments would be filled in with metavariables if we created the
`Expr` objects immediately, so instead we return thunks that generate the expressions
on demand. This is the first component, with type `List (TermElabM Expr)`.

As an example, we have `def rfl : ∀ {α : Sort u} {a : α}, a = a`, which on elaboration will become
`@rfl ?m_1 ?m_2`.

Because `solve_by_elim` works by repeated application of lemmas against subgoals,
the first time such a lemma is successfully applied,
those metavariables will be unified, and thereafter have fixed values.
This would make it impossible to apply the lemma
a second time with different values of the metavariables.

See https://github.com/leanprover-community/mathlib/issues/2269

### Relevant local hypotheses

`solve_by_elim*` works with multiple goals,
and we need to use separate sets of local hypotheses for each goal.
The second component of the returned value provides these local hypotheses.
(Essentially using `getLocalHyps`, along with some filtering to remove hypotheses
that have been explicitly removed via `only` or `[-h]`.)

-/
-- These `TermElabM`s must be run inside a suitable `g.withContext`,
-- usually using `elabContextLemmas`.
def mkAssumptionSet (noDefaults star : Bool) (add remove : List Term) (use : Array Ident) :
    MetaM (List (TermElabM Expr) × (SolveByElimConfig → TermElabM (List Expr))) := do
  if star && !noDefaults then
    throwError "It doesn't make sense to use `*` without `only`."

  let defaults : List (TermElabM Expr) :=
    [← `(rfl), ← `(trivial), ← `(congrFun), ← `(congrArg)].map elab'
  let labelledLemmas := (← use.mapM (Lean.labelled ·.raw.getId)).flatten.toList
    |>.map (liftM <| mkConstWithFreshMVarLevels ·)
  let lemmas := if noDefaults then
    add.map elab' ++ labelledLemmas
  else
    add.map elab' ++ labelledLemmas ++ defaults

  if !remove.isEmpty && noDefaults && !star then
    throwError "It doesn't make sense to remove local hypotheses when using `only` without `*`."
  let locals (cfg : SolveByElimConfig) : TermElabM (List Expr) :=
    if noDefaults && !star then do pure []
    else do saturateSymm cfg.symm <| (← getLocalHyps).toList.removeAll (← remove.mapM elab')

  return (lemmas, locals)
where
  /-- Run `elabTerm`. -/
  elab' (t : Term) : TermElabM Expr := Elab.Term.elabTerm t.raw none

open Syntax
