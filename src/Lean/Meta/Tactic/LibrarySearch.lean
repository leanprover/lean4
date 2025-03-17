/-
Copyright (c) 2021-2023 Gabriel Ebner and Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Joe Hendrix, Kim Morrison
-/
prelude
import Init.Data.Nat.MinMax
import Lean.Meta.LazyDiscrTree
import Lean.Meta.Tactic.SolveByElim
import Lean.Util.Heartbeats

/-!
# Library search

This file defines tactics `exact?` and `apply?`,
(formerly known as `library_search`)
and a term elaborator `exact?%`
that tries to find a lemma
solving the current goal
(subgoals are solved using `solveByElim`).

```
example : x < x + 1 := exact?%
example : Nat := by exact?
```
-/


namespace Lean.Meta.LibrarySearch

builtin_initialize registerTraceClass `Tactic.librarySearch
builtin_initialize registerTraceClass `Tactic.librarySearch.lemmas

open SolveByElim

/--
Wrapper for calling `Lean.Meta.SolveByElim.solveByElim with
appropriate arguments for library search.
-/
def solveByElim (required : List Expr) (exfalso : Bool) (goals : List MVarId) (maxDepth : Nat) := do
  let cfg : SolveByElimConfig :=
    { maxDepth, exfalso := exfalso, symm := true, commitIndependentGoals := true,
      transparency := ← getTransparency,
      -- `constructor` has been observed to significantly slow down `exact?` in Mathlib.
      constructor := false }
  let ⟨lemmas, ctx⟩ ← SolveByElim.mkAssumptionSet false false [] [] #[]
  let cfg := if !required.isEmpty then cfg.requireUsingAll required else cfg
  SolveByElim.solveByElim cfg lemmas ctx goals

/--
A "modifier" for a declaration.
* `none` indicates the original declaration,
* `mp` indicates that (possibly after binders) the declaration is an `↔`,
  and we want to consider the forward direction,
* `mpr` similarly, but for the backward direction.
-/
inductive DeclMod
  | /-- the original declaration -/ none
  | /-- the forward direction of an `iff` -/ mp
  | /-- the backward direction of an `iff` -/ mpr
deriving DecidableEq, Inhabited, Ord, Hashable

/--
LibrarySearch has an extension mechanism for replacing the function used
to find candidate lemmas.
-/
@[reducible]
def CandidateFinder := Expr → MetaM (Array (Name × DeclMod))

open LazyDiscrTree (InitEntry findMatches)

private def addImport (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (InitEntry (Name × DeclMod))) :=
  forallTelescope constInfo.type fun _ type => do
    let e ← InitEntry.fromExpr type (name, DeclMod.none)
    let a := #[e]
    if e.key == .const ``Iff 2 then
      let a := a.push (←e.mkSubEntry 0 (name, DeclMod.mp))
      let a := a.push (←e.mkSubEntry 1 (name, DeclMod.mpr))
      pure a
    else
      pure a

/-- Stores import discrimination tree. -/
private def LibSearchState := IO.Ref (Option (LazyDiscrTree (Name × DeclMod)))

private builtin_initialize defaultLibSearchState : IO.Ref (Option (LazyDiscrTree (Name × DeclMod))) ← do
  IO.mkRef .none

private instance : Inhabited LibSearchState where
  default := defaultLibSearchState

private builtin_initialize ext : EnvExtension LibSearchState ←
  registerEnvExtension (IO.mkRef .none)

/--
We drop `.star` and `Eq * * *` from the discriminator trees because
they match too much.
-/
def droppedKeys : List (List LazyDiscrTree.Key) := [[.star], [.const `Eq 3, .star, .star, .star]]

/--
The maximum number of constants an individual task may perform.

The value was picked because it roughly corresponded to 50ms of work on the
machine this was developed on.  Smaller numbers did not seem to improve
performance when importing Std and larger numbers (<10k) seemed to degrade
initialization performance.
-/
private def constantsPerImportTask : Nat := 6500

/-- Create function for finding relevant declarations. -/
def libSearchFindDecls : Expr → MetaM (Array (Name × DeclMod)) :=
  findMatches ext addImport
      (droppedKeys := droppedKeys)
      (constantsPerTask := constantsPerImportTask)

/--
Return an action that returns true when the remaining heartbeats is less
than the currently remaining heartbeats * leavePercent / 100.
-/
def mkHeartbeatCheck (leavePercent : Nat) : MetaM (MetaM Bool) := do
  let maxHB ← getMaxHeartbeats
  let hbThreshold := (← getRemainingHeartbeats) * leavePercent / 100
  -- Return true if we should stop
  pure $
    if maxHB = 0 then
      pure false
    else do
      return (← getRemainingHeartbeats) < hbThreshold

private def librarySearchEmoji : Except ε (Option α) → String
| .error _ => bombEmoji
| .ok (some _) => crossEmoji
| .ok none => checkEmoji

/--
Interleave x y interleaves the elements of x and y until one is empty and then returns
final elements in other list.
-/
def interleaveWith {α β γ} (f : α → γ) (x : Array α) (g : β → γ) (y : Array β) : Array γ :=
    Id.run do
  let mut res := Array.mkEmpty (x.size + y.size)
  let n := min x.size y.size
  for h : i in [0:n] do
    have p : i < min x.size y.size := h.2.1
    have q : i < x.size := Nat.le_trans p (Nat.min_le_left ..)
    have r : i < y.size := Nat.le_trans p (Nat.min_le_right ..)
    res := res.push (f x[i])
    res := res.push (g y[i])
  let last :=
        if x.size > n then
          (x.extract n x.size).map f
        else
          (y.extract n y.size).map g
  pure $ res ++ last

/--
An exception ID that indicates further speculation on candidate lemmas should stop
and current results should be returned.
-/
private builtin_initialize abortSpeculationId : InternalExceptionId ←
  registerInternalExceptionId `Lean.Meta.LibrarySearch.abortSpeculation

/--
Called to abort speculative execution in library search.
-/
def abortSpeculation [MonadExcept Exception m] : m α :=
  throw (Exception.internal abortSpeculationId {})

/-- Returns true if this is an abort speculation exception. -/
def isAbortSpeculation : Exception → Bool
| .internal id _ => id == abortSpeculationId
| _ => false

section LibrarySearch

/--
A library search candidate using symmetry includes the goal to solve, the metavar
context for that goal, and the name and orientation of a rule to try using with goal.
-/
@[reducible]
def Candidate :=  (MVarId × MetavarContext) × (Name × DeclMod)

/--
Run `searchFn` on both the goal and `symm` applied to the goal.
-/
def librarySearchSymm (searchFn : CandidateFinder) (goal : MVarId) : MetaM (Array Candidate) := do
  let tgt ← goal.getType
  let l1 ← searchFn tgt
  let coreMCtx ← getMCtx
  let coreGoalCtx := (goal, coreMCtx)
  if let some symmGoal ← observing? goal.applySymm then
    let newType ← instantiateMVars  (← symmGoal.getType)
    let l2 ← searchFn newType
    let symmMCtx ← getMCtx
    let symmGoalCtx := (symmGoal, symmMCtx)
    setMCtx coreMCtx
    pure $ interleaveWith (coreGoalCtx, ·) l1 (symmGoalCtx, ·) l2
  else
    pure $ l1.map (coreGoalCtx, ·)

private def emoji (e : Except ε α) := if e.toBool then checkEmoji else crossEmoji

/-- Create lemma from name and mod. -/
def mkLibrarySearchLemma (lem : Name) (mod : DeclMod) : MetaM Expr := do
  let lem ← mkConstWithFreshMVarLevels lem
  match mod with
  | .none => pure lem
  | .mp => mapForallTelescope (fun e => mkAppM ``Iff.mp #[e]) lem
  | .mpr => mapForallTelescope (fun e => mkAppM ``Iff.mpr #[e]) lem

private def isVar (e : Expr) : Bool :=
  match e with
  | .bvar _ => true
  | .fvar _ => true
  | .mvar _ => true
  | _ => false

/--
Tries to apply the given lemma (with symmetry modifier) to the goal,
then tries to close subsequent goals using `solveByElim`.
If `solveByElim` succeeds, `[]` is returned as the list of new subgoals,
otherwise the full list of subgoals is returned.
-/
private def librarySearchLemma (cfg : ApplyConfig) (act : List MVarId → MetaM (List MVarId))
    (allowFailure : MVarId → MetaM Bool) (cand : Candidate)  : MetaM (List MVarId) := do
  let ((goal, mctx), (name, mod)) := cand
  let ppMod (mod : DeclMod) : MessageData :=
        match mod with | .none => "" | .mp => " with mp" | .mpr => " with mpr"
  withTraceNode `Tactic.librarySearch (return m!"{emoji ·} trying {name}{ppMod mod} ") do
    setMCtx mctx
    let lem ← mkLibrarySearchLemma name mod
    let newGoals ← goal.apply lem cfg
    try
      act newGoals
    catch _ =>
      if ← allowFailure goal then
        pure newGoals
      else
        failure

/--
Sequentially invokes a tactic `act` on each value in candidates on the current state.

The tactic `act` should return a list of meta-variables that still need to be resolved.
If this list is empty, then no variables remain to be solved, and `tryOnEach` returns
`none` with the environment set so each goal is resolved.

If the action throws an internal exception with the `abortSpeculationId` id then
further computation is stopped and intermediate results returned. If any other
exception is thrown, then it is silently discarded.
-/
def tryOnEach
    (act : Candidate → MetaM (List MVarId))
    (candidates : Array Candidate) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  let mut a := #[]
  let s ← saveState
  for c in candidates do
    match ← (tryCatch (Except.ok <$> act c) (pure ∘ Except.error)) with
    | .error e =>
      restoreState s
      if isAbortSpeculation e then
        break
    | .ok remaining =>
      if remaining.isEmpty then
        return none
      let ctx ← getMCtx
      restoreState s
      a := a.push (remaining, ctx)
  return (.some a)

private def librarySearch' (goal : MVarId)
    (tactic : List MVarId → MetaM (List MVarId))
    (allowFailure : MVarId → MetaM Bool)
    (leavePercentHeartbeats : Nat) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  withTraceNode `Tactic.librarySearch (return m!"{librarySearchEmoji ·} {← goal.getType}") do
  profileitM Exception "librarySearch" (← getOptions) do
    -- Create predicate that returns true when running low on heartbeats.
    let candidates ← librarySearchSymm libSearchFindDecls goal
    let cfg : ApplyConfig := { allowSynthFailures := true }
    let shouldAbort ← mkHeartbeatCheck leavePercentHeartbeats
    let act := fun cand => do
        if ←shouldAbort then
          abortSpeculation
        librarySearchLemma cfg tactic allowFailure cand
    tryOnEach act candidates

/--
Tries to solve the goal either by:
* calling `tactic true`
* or applying a library lemma then calling `tactic false` on the resulting goals.

Typically here `tactic` is `solveByElim`,
with the `Bool` flag indicating whether it may retry with `exfalso`.

If it successfully closes the goal, returns `none`.
Otherwise, it returns `some a`, where `a : Array (List MVarId × MetavarContext)`,
with an entry for each library lemma which was successfully applied,
containing a list of the subsidiary goals, and the metavariable context after the application.

(Always succeeds, and the metavariable context stored in the monad is reverted,
unless the goal was completely solved.)

(Note that if `solveByElim` solves some but not all subsidiary goals,
this is not currently tracked.)
-/
def librarySearch (goal : MVarId)
    (tactic : Bool → List MVarId → MetaM (List MVarId) :=
      fun initial g => solveByElim [] (maxDepth := 6) (exfalso := initial) g)
    (allowFailure : MVarId → MetaM Bool := fun _ => pure true)
    (leavePercentHeartbeats : Nat := 10) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  (tactic true [goal] *> pure none) <|>
  librarySearch' goal (tactic false) allowFailure leavePercentHeartbeats

end LibrarySearch

end Lean.Meta.LibrarySearch
