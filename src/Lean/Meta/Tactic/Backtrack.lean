/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.BasicAux
import Lean.Meta.Iterator
import Lean.Meta.Tactic.IndependentOf

/-!
# `backtrack`

A meta-tactic for running backtracking search, given a non-deterministic tactic
`alternatives : MVarId → Nondet MetaM (List MVarId)`.

`backtrack alternatives goals` will recursively try to solve all goals in `goals`,
and the subgoals generated, backtracking as necessary.

In its default behaviour, it will either solve all goals, or fail.
A customisable `suspend` hook in `BacktrackConfig` allows suspend a goal (or subgoal),
so that it will be returned instead of processed further.
Other hooks `proc` and `discharge` (described in `BacktrackConfig`) allow running other
tactics before `alternatives`, or if all search branches from a given goal fail.

Currently only `solveByElim` is implemented in terms of `backtrack`.
-/

namespace Lean.Meta.Tactic.Backtrack

open Lean Meta

/--
Configuration structure to control the behaviour of `backtrack`:
* control the maximum depth and behaviour (fail or return subgoals) at the maximum depth,
* and hooks allowing
  * modifying intermediate goals before running the external tactic,
  * 'suspending' goals, returning them in the result, and
  * discharging subgoals if the external tactic fails.
-/
structure BacktrackConfig where
  /-- Maximum recursion depth. -/
  maxDepth : Nat := 6
  /-- An arbitrary procedure which can be used to modify the list of goals
  before each attempt to generate alternatives.
  Called as `proc goals curr`, where `goals` are the original goals for `backtracking`,
  and `curr` are the current goals.
  Returning `some l` will replace the current goals with `l` and recurse
  (consuming one step of maximum depth).
  Returning `none` will proceed to generating alternative without changing goals.
  Failure will cause backtracking.
  (defaults to `none`) -/
  proc : List MVarId → List MVarId → MetaM (Option (List MVarId)) := fun _ _ => pure none
  /-- If `suspend g`, then we do not consider alternatives for `g`,
  but return `g` as a new subgoal. (defaults to `false`) -/
  suspend : MVarId → MetaM Bool := fun _ => pure false
  /-- `discharge g` is called on goals for which there were no alternatives.
  If `none` we return `g` as a new subgoal.
  If `some l`, we replace `g` by `l` in the list of active goals, and recurse.
  If failure, we backtrack. (defaults to failure) -/
  discharge : MVarId → MetaM (Option (List MVarId)) := fun _ => failure
  /--
  If we solve any "independent" goals, don't fail.
  See `Lean.MVarId.independent?` for the definition of independence.
  -/
  commitIndependentGoals : Bool := false

namespace Backtrack

/--
Pretty print a list of goals.
-/
private def ppMVarId (g : MVarId) : MetaM Format := ppExpr =<< g.getType

/--
Pretty print a list of goals.
-/
private def ppMVarIds (gs : List MVarId) : MetaM (List Format) := gs.mapM ppMVarId

/-- Run a monadic function on every element of a list,
returning the list of elements on which the function fails, and the list of successful results. -/
def tryAllM [Monad m] [Alternative m] (L : List α) (f : α → m β) : m (List α × List β) := do
  let R ← L.mapM (fun a => (Sum.inr <$> f a) <|> (pure (Sum.inl a)))
  return (R.filterMap (fun s => match s with | .inl a => a | _ => none),
    R.filterMap (fun s => match s with | .inr b => b | _ => none))

variable (cfg : BacktrackConfig)
variable (trace : Name := .anonymous)
variable (next : MVarId → (List MVarId → MetaM (Option (List MVarId))) → MetaM (List MVarId))

/--
* `n : Nat` steps remaining.
* `curr : List MVarId` the current list of unsolved goals.
* `acc : List MVarId` a list of "suspended" goals, which will be returned as subgoals.
-/
  -- `acc` is intentionally a `List` rather than an `Array` so we can share across branches.
private def run (goals : List MVarId) (n : Nat) (curr acc : List MVarId) : MetaM (List MVarId) := do
  match n with
  | 0 => do
    -- We're out of fuel.
    throwError "backtrack exceeded the recursion limit"
  | n + 1 => do
  -- First, run `cfg.proc`, to see if it wants to modify the goals.
  let procResult? ← try
    cfg.proc goals curr
  catch e =>
    withTraceNode trace
      (return m!"{exceptEmoji ·} BacktrackConfig.proc failed: {e.toMessageData}") do
    throw e
  match procResult? with
  | some curr' => run goals n curr' acc
  | none =>
  match curr with
  -- If there are no active goals, return the accumulated goals.
  | [] => withTraceNode trace (return m!"{exceptEmoji ·} success!") do
      return acc.reverse
  | g :: gs =>
  -- Discard any goals which have already been assigned.
  if ← g.isAssigned then
    withTraceNode trace (return m!"{exceptEmoji ·} discarding already assigned goal {g}") do
      run goals (n+1) gs acc
  else
  withTraceNode trace
    -- Note: the `addMessageContextFull` ensures we show the goal using the mvar context before
    -- the `do` block below runs, potentially unifying mvars in the goal.
    (return m!"{exceptEmoji ·} working on: {← addMessageContextFull g}")
    do
      -- Check if we should suspend the search here:
      if (← cfg.suspend g) then
        withTraceNode trace
          (fun _ => return m!"⏸️ suspending search and returning as subgoal") do
        run goals (n+1) gs (g :: acc)
      else
        try
          -- We attempt to find an alternative,
          -- for which all resulting sub-goals can be discharged using `run n`.
          next g (fun r => observing? do run goals n (r ++ gs) acc)
        catch _ =>
          -- No lemmas could be applied:
          match (← cfg.discharge g) with
          | none => (withTraceNode trace
              (fun _ => return m!"⏭️ deemed acceptable, returning as subgoal") do
            run goals (n+1) gs (g :: acc))
          | some l => (withTraceNode trace
              (fun _ => return m!"⏬ discharger generated new subgoals") do
            run goals n (l ++ gs) acc)

/--
A wrapper around `run`, which works on "independent" goals separately first,
to reduce backtracking.
-/
private partial def processIndependentGoals (orig : List MVarId) (goals remaining : List MVarId) :
    MetaM (List MVarId) := do
  -- Partition the remaining goals into "independent" goals
  -- (which should be solvable without affecting the solvability of other goals)
  -- and all the others.
  let (igs, ogs) ← remaining.partitionM (MVarId.isIndependentOf goals)
  if igs.isEmpty then
    -- If there are no independent goals, we solve all the goals together via backtracking search.
    return (← run cfg trace next orig cfg.maxDepth remaining [])
  else
    withTraceNode trace
      (fun _ => return m!"independent goals {← ppMVarIds igs},"
        ++ m!" working on them before {← ppMVarIds ogs}") do
    -- Invoke `run` on each of the independent goals separately,
    -- gathering the subgoals on which `run` fails,
    -- and the new subgoals generated from goals on which it is successful.
    let (failed, newSubgoals') ← tryAllM igs fun g =>
      run cfg trace next orig cfg.maxDepth [g] []
    let newSubgoals := newSubgoals'.flatten
    withTraceNode trace
      (fun _ => return m!"failed: {← ppMVarIds failed}, new: {← ppMVarIds newSubgoals}") do
    -- Update the list of goals with respect to which we need to check independence.
    let goals' := (← goals.filterM (fun g => do pure !(← g.isAssigned))) ++ newSubgoals
    -- If `commitIndependentGoals` is `true`, we will return the new goals
    -- regardless of whether we can make further progress on the other goals.
    if cfg.commitIndependentGoals && !newSubgoals.isEmpty then
      return newSubgoals ++ failed ++ (← (processIndependentGoals orig goals' ogs <|> pure ogs))
    else if !failed.isEmpty then
      -- If `commitIndependentGoals` is `false`, and we failed on any of the independent goals,
      -- then overall failure is inevitable so we can stop here.
      failure
    else
      -- Finally, having solved this batch of independent goals,
      -- recurse (potentially now finding new independent goals).
      return newSubgoals ++ (← processIndependentGoals orig goals' ogs)

end Backtrack


/--
Attempts to solve the `goals`, by recursively calling `next` on each
subgoal that appears with a callback to reenter backtracking search.

Further flow control options are available via the `Config` argument.

Returns a list of subgoals which were "suspended" via the `suspend` or
`discharge` hooks in `Config`. In the default configuration, `backtrack`
will either return an empty list or fail.
-/
def backtrack (cfg : BacktrackConfig := {}) (trace : Name := .anonymous)
    (next : MVarId → MetaM (Meta.Iterator (List MVarId)))
    (goals : List MVarId) : MetaM (List MVarId) := do
  let resolve g f := do (←next g).firstM f
  Backtrack.processIndependentGoals cfg trace resolve goals goals goals
