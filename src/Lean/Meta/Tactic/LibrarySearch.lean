/-
Copyright (c) 2021-2023 Gabriel Ebner and Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Joe Hendrix, Kim Morrison
-/
module

prelude
public import Lean.Meta.LazyDiscrTree
public import Lean.Meta.Tactic.SolveByElim
public import Lean.Meta.Tactic.Grind.Main
public import Lean.Util.Heartbeats
import Init.Grind.Util
import Init.Try
import Lean.Elab.Tactic.Basic
import Lean.Linter.Deprecated

public section

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
A discharger that tries `grind` on the goal.
The proof is wrapped in `Grind.Marker` so that suggestions display `(by grind)`
instead of the complex grind proof term.
Returns `some []` if grind succeeds, `none` otherwise (leaving the goal as a subgoal).
-/
def grindDischarger (mvarId : MVarId) : MetaM (Option (List MVarId)) := do
  try
    -- Apply the marker wrapper, creating a subgoal for grind to solve
    let type ← mvarId.getType
    let u ← getLevel type
    let markerExpr := mkApp (.const ``Lean.Grind.Marker [u]) type
    let [subgoal] ← mvarId.apply markerExpr
      | return none
    -- Solve the subgoal with grind
    let params ← Grind.mkDefaultParams {}
    let result ← Grind.main subgoal params
    if result.hasFailed then
      return none
    else
      return some []
  catch _ =>
    return none

/--
A discharger that tries `try?` on the goal.
The proof is wrapped in `Try.Marker` so that suggestions display `(by try?)`
instead of the complex proof term.
Returns `some []` if try? succeeds, `none` otherwise (leaving the goal as a subgoal).
-/
def tryDischarger (mvarId : MVarId) : MetaM (Option (List MVarId)) := do
  try
    -- Apply the marker wrapper, creating a subgoal for try? to solve
    let type ← mvarId.getType
    let u ← getLevel type
    let markerExpr := mkApp (.const ``Lean.Try.Marker [u]) type
    let [subgoal] ← mvarId.apply markerExpr
      | return none
    -- Run try? via TacticM to solve the subgoal
    -- We suppress the "Try this" messages since we're using try? as a discharger
    let tacStx ← `(tactic| try?)
    let remainingGoals ← Elab.Term.TermElabM.run' <| Elab.Tactic.run subgoal do
      -- Suppress info messages from try?
      Elab.Tactic.withSuppressedMessages do
        Elab.Tactic.evalTactic tacStx
    if remainingGoals.isEmpty then
      return some []
    else
      return none
  catch _ =>
    return none

/--
Wrapper for calling `Lean.Meta.SolveByElim.solveByElim with
appropriate arguments for library search.

If `grind` is true, `grind` will be used as a fallback discharger for subgoals
that cannot be closed by other means.
If `try?` is true, `try?` will be used as a fallback discharger (via grind internally).
-/
def solveByElim (required : List Expr) (exfalso : Bool) (goals : List MVarId)
    (maxDepth : Nat) (grind : Bool := false) (try? : Bool := false) := do
  let cfg : SolveByElimConfig :=
    { maxDepth, exfalso := exfalso, symm := true, commitIndependentGoals := true,
      transparency := ← getTransparency,
      -- `constructor` has been observed to significantly slow down `exact?` in Mathlib.
      constructor := false }
  -- Add grind or try? as a fallback discharger (tried after intro/constructor fail)
  let cfg := if try? then cfg.withDischarge tryDischarger
             else if grind then cfg.withDischarge grindDischarger
             else cfg
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
@[reducible, expose] def CandidateFinder := Expr → MetaM (Array (Name × DeclMod))

open LazyDiscrTree (InitEntry findMatches)

private def addImport (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (InitEntry (Name × DeclMod))) := do
  -- Don't report deprecated lemmas.
  if Linter.isDeprecated (← getEnv) name then return #[]
  -- Don't report lemmas from metaprogramming namespaces.
  if name.isMetaprogramming then return #[] else
  forallTelescope constInfo.type fun _ type => do
    let e ← InitEntry.fromExpr type (name, DeclMod.none)
    let a := #[e]
    if e.key == .const ``Iff 2 then
      let a := a.push (← e.mkSubEntry 0 (name, DeclMod.mp))
      let a := a.push (← e.mkSubEntry 1 (name, DeclMod.mpr))
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

/-- Environment extension for caching star-indexed lemmas.
    Used for fallback when primary search finds nothing for fvar-headed goals. -/
private builtin_initialize starLemmasExt : EnvExtension (IO.Ref (Option (Array (Name × DeclMod)))) ←
  registerEnvExtension (IO.mkRef .none)

/-- Create function for finding relevant declarations.
    Also captures dropped entries in starLemmasExt for fallback search. -/
def libSearchFindDecls (ty : Expr) : MetaM (Array (Name × DeclMod)) := do
  let _ : Inhabited (IO.Ref (Option (Array (Name × DeclMod)))) := ⟨← IO.mkRef none⟩
  let droppedRef := starLemmasExt.getState (←getEnv)
  findMatches ext addImport
      (droppedKeys := droppedKeys)
      (constantsPerTask := constantsPerImportTask)
      (droppedEntriesRef := some droppedRef)
      ty

/-- Get star-indexed lemmas (lazily computed during tree initialization). -/
def getStarLemmas : MetaM (Array (Name × DeclMod)) := do
  let _ : Inhabited (IO.Ref (Option (Array (Name × DeclMod)))) := ⟨← IO.mkRef none⟩
  let ref := starLemmasExt.getState (←getEnv)
  match ←ref.get with
  | some lemmas => return lemmas
  | none =>
    -- If star lemmas aren't cached yet, trigger tree initialization by searching for a dummy type
    -- This will populate starLemmasExt as a side effect
    let _ ← libSearchFindDecls (mkConst ``True)
    pure ((←ref.get).getD #[])

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
  for h : i in *...n do
    have p : i < min x.size y.size := Std.Rio.lt_upper_of_mem h
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
@[reducible, expose] def Candidate :=  (MVarId × MetavarContext) × (Name × DeclMod)

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
`none` with the environment set so each goal is resolved (unless `collectAll` is true,
in which case it continues searching and collects complete solutions in the array).

If the action throws an internal exception with the `abortSpeculationId` id then
further computation is stopped and intermediate results returned. If any other
exception is thrown, then it is silently discarded.
-/
def tryOnEach
    (act : Candidate → MetaM (List MVarId))
    (candidates : Array Candidate)
    (collectAll : Bool := false) :
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
      if remaining.isEmpty && !collectAll then
        return none
      let ctx ← getMCtx
      restoreState s
      a := a.push (remaining, ctx)
  return (.some a)

private def librarySearch' (goal : MVarId)
    (tactic : List MVarId → MetaM (List MVarId))
    (allowFailure : MVarId → MetaM Bool)
    (leavePercentHeartbeats : Nat)
    (includeStar : Bool := true)
    (collectAll : Bool := false) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  withTraceNode `Tactic.librarySearch (return m!"{librarySearchEmoji ·} {← goal.getType}") do
  profileitM Exception "librarySearch" (← getOptions) do
    let cfg : ApplyConfig := { allowSynthFailures := true }
    let shouldAbort ← mkHeartbeatCheck leavePercentHeartbeats
    let act := fun cand => do
        if ←shouldAbort then
          abortSpeculation
        librarySearchLemma cfg tactic allowFailure cand
    -- First pass: search with droppedKeys (excludes star-indexed lemmas)
    let candidates ← librarySearchSymm libSearchFindDecls goal
    match ← tryOnEach act candidates collectAll with
    | none => return none  -- Found a complete solution (only when collectAll = false)
    | some results =>
      -- Only do star fallback if:
      -- 1. No complete solutions from primary search (when collectAll, check for empty remaining)
      -- 2. includeStar is true
      -- When collectAll = false, any result means we should skip star fallback (return partial).
      -- When collectAll = true, we continue to star lemmas unless we have a complete solution.
      let hasCompleteSolution := results.any (·.1.isEmpty)
      if hasCompleteSolution || (!collectAll && !results.isEmpty) || !includeStar then
        return some results
      -- Second pass: try star-indexed lemmas (those with [*] or [Eq,*,*,*] keys)
      -- No need for librarySearchSymm since getStarLemmas ignores the goal type
      let starLemmas ← getStarLemmas
      if starLemmas.isEmpty then return some results
      let mctx ← getMCtx
      let starCandidates := starLemmas.map ((goal, mctx), ·)
      match ← tryOnEach act starCandidates collectAll with
      | none => return none  -- Found complete solution from star lemmas
      | some starResults => return some (results ++ starResults)

/--
Tries to solve the goal by applying a library lemma
then calling `tactic` on the resulting goals.

Typically here `tactic` is `solveByElim`.

If it successfully closes the goal, returns `none` (unless `collectAll` is true).
Otherwise, it returns `some a`, where `a : Array (List MVarId × MetavarContext)`,
with an entry for each library lemma which was successfully applied,
containing a list of the subsidiary goals, and the metavariable context after the application.
When `collectAll` is true, complete solutions (with empty remaining goals) are also included
in the array instead of returning early.

(Always succeeds, and the metavariable context stored in the monad is reverted,
unless the goal was completely solved.)

(Note that if `solveByElim` solves some but not all subsidiary goals,
this is not currently tracked.)
-/
def librarySearch (goal : MVarId)
    (tactic : List MVarId → MetaM (List MVarId) :=
      fun g => solveByElim [] (maxDepth := 6) (exfalso := false) g)
    (allowFailure : MVarId → MetaM Bool := fun _ => pure true)
    (leavePercentHeartbeats : Nat := 10)
    (includeStar : Bool := true)
    (collectAll : Bool := false) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  librarySearch' goal tactic allowFailure leavePercentHeartbeats includeStar collectAll

end LibrarySearch

end Lean.Meta.LibrarySearch
