import Lean.Meta.Tactic.LibrarySearch
import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.BuiltinTactic

namespace Lean.Elab.LibrarySearch

open Lean Meta LibrarySearch
open Elab Tactic TryThis


-- TODO: implement the additional options for `library_search` from Lean 3,
-- in particular including additional lemmas
-- with `std_exact? [X, Y, Z]` or `std_exact? with attr`.

-- For now we only implement the basic functionality.
-- The full syntax is recognized, but will produce a "Tactic has not been implemented" error.

/-- Implementation of the `exact?` tactic. -/
def exact? (tk : Syntax) (required : Option (Array (TSyntax `term)))
   (solver : Option (TSyntax `Lean.Parser.Tactic.tacticSeq)) (requireClose : Bool) :
    TacticM Unit := do
  let mvar ← getMainGoal
  let (_, goal) ← (← getMainGoal).intros
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    let tactic ←
      match solver with
      | none =>
        pure (fun exfalso => solveByElim required (exfalso := exfalso) (maxDepth := 6))
      | some t =>
        let _ <- mkInitialTacticInfo t
        throwError "Do not yet support custom std_exact?/std_apply? tactics."
    let allowFailure := fun g => do
      let g ← g.withContext (instantiateMVars (.mvar g))
      return required.all fun e => e.occurs g
    match ← librarySearch goal tactic allowFailure with
    -- Found goal that closed problem
    | none =>
      addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta
    -- Found suggestions
    | some suggestions =>
      if requireClose then throwError
        "`std_exact?` could not close the goal. Try `std_apply?` to see partial suggestions."
      reportOutOfHeartbeats `library_search tk
      for (_, suggestionMCtx) in suggestions do
        withMCtx suggestionMCtx do
          addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta (addSubgoalsMsg := true)
      if suggestions.isEmpty then logError "std_apply? didn't find any relevant lemmas"
      admitGoal goal

/-- Syntax for `exact?` -/
syntax (name := exact?') "exact?" (" using " (colGt ident),+)?
    ("=>" tacticSeq)? : tactic

elab_rules : tactic
  | `(tactic| exact? $[using $[$lemmas],*]? $[=> $solver]?) => do
  exact? (← getRef) lemmas solver true

/-- Syntax for `apply?` -/
syntax (name := apply?') "apply?" (" using " (colGt term),+)? : tactic

elab_rules : tactic | `(tactic| apply? $[using $[$required],*]?) => do
  exact? (← getRef) required none false

/-- Term elaborator using the `exact?` tactic. -/
elab tk:"std_exact?%" : term <= expectedType => do
  let goal ← mkFreshExprMVar expectedType
  let (_, introdGoal) ← goal.mvarId!.intros
  introdGoal.withContext do
    let tactic := fun exfalso g => solveByElim []  (maxDepth := 6) exfalso g
    if let some suggestions ← librarySearch introdGoal tactic then
      reportOutOfHeartbeats `library_search tk
      for suggestion in suggestions do
        withMCtx suggestion.2 do
          addTermSuggestion tk (← instantiateMVars goal).headBeta
      if suggestions.isEmpty then logError "std_exact? didn't find any relevant lemmas"
      mkSorry expectedType (synthetic := true)
    else
      addTermSuggestion tk (← instantiateMVars goal).headBeta
      instantiateMVars goal

end Lean.Elab.LibrarySearch
