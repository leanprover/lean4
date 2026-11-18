/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.ExprPattern

public section

namespace Lean.Elab.Tactic

/--
Try `f h ty` on each non-implementation-detail hypothesis `(h, ty)` of the main goal and return
the first succeeding result `some r`.

Hypotheses are tried newest first by default (`reverse := true`, matching Rocq `match goal`); pass
`reverse := false` for oldest first. Free variables listed in `except` are skipped (useful when
nesting `firstHyp` calls with `except := [h1]` to match multiple distinct hypotheses), and assigned
metavariables in `ty` are instantiated before `f` is invoked inside the main goal's local context
(`withMainContext` is handled automatically).

Execution runs inside `Term.withoutTacticIncrementality true`, `Term.withoutErrToSorry`, and
`withoutRecover`. If an arm fails, `Tactic.SavedState` is atomically rolled back with
`restoreInfo := true`—reverting metavariable assignments, goal list edits, message log entries,
term elaboration state, and info trees without admitting `sorry` or leaking errors—before trying
the next hypothesis. Returns `none` if no hypothesis succeeds.
-/
def firstHyp? (f : Expr → Expr → TacticM α)
    (reverse : Bool := true) (except : List Expr := []) : TacticM (Option α) :=
  Term.withoutTacticIncrementality true <| Term.withoutErrToSorry <| withoutRecover do
    (← getMainGoal).firstHyp? (reverse := reverse) (except := except) fun h ty => do
      let s ← saveState
      Tactic.tryCatch (f h ty) fun ex => do
        s.restore (restoreInfo := true)
        throw ex

/--
Like `Lean.Elab.Tactic.firstHyp?`, but throws `"firstHyp: no hypothesis matched"` if no
hypothesis succeeds.
-/
def firstHyp (f : Expr → Expr → TacticM α)
    (reverse : Bool := true) (except : List Expr := []) : TacticM α := do
  match ← firstHyp? f (reverse := reverse) (except := except) with
  | some a => return a
  | none   => throwError "firstHyp: no hypothesis matched"

end Lean.Elab.Tactic
