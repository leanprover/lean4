import Lean.LibrarySuggestions.Basic

/-!
Regression test: `MVarId.getRelevantConstants` must instantiate metavariables
in the goal type before collecting constants.

A goal reached via `induction` has type `?motive arg`, where `?motive` is an
assigned-but-unsubstituted metavariable. Without `instantiateMVars`, the
constant fold treats `?motive` as an opaque leaf, so every constant occurring
in the goal predicate is lost.
-/

open Lean Lean.Elab.Tactic

axiom MyP : Nat → Prop

example : ∀ n : Nat, MyP n := by
  intro n
  induction n with
  | zero =>
    run_tac do
      let c ← (← getMainGoal).getRelevantConstants
      unless c.contains ``MyP do
        throwError "getRelevantConstants missed `MyP` hidden behind the \
          induction motive metavariable"
    sorry
  | succ k ih => sorry
