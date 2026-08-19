/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.Basic

public section

namespace Lean.Elab.Do

open Lean Meta Parser.Term

/-!
What the clauses of a contract share. A clause states an assertion of the `do` block's monad, and
`WPMonad` computes the type of that assertion.
-/

/-- The assertion language of the `do` block's monad, which `WPMonad` computes as an output
parameter: synthesizing `WPMonad StateM Nat _ _` assigns `Nat → Prop` for the assertions of
`StateM Nat`. The result is what the monad's assertions are known to be right here, so a monad
whose instance is not available reports nothing. The type is built from syntax so that the
universes and the instance arguments of the class come from elaboration. -/
def assertionLanguage? : DoElabM (Option Expr) := do
  let wpMonad := `Std.WP.WPMonad
  unless (← getEnv).contains wpMonad do return none
  let wpTy ← Term.elabType <| ←
    `($(mkIdent wpMonad) $(← Term.exprToSyntax (← read).monadInfo.m) _ _)
  let .some _ ← trySynthInstance wpTy | return none
  let some pred := wpTy.getAppArgs[1]? | return none
  let pred ← instantiateMVars pred
  return if pred.hasExprMVar then none else some pred

/-- Ascribe the first `n` argument types of the assertion language to `f`, so that a binder may
destructure its argument: `fun ⟨lo, hi⟩ => lo ≤ hi` is stated at `Nat × Nat → _`. The result is a
hole, because a `decreasing` measure ends in the measure type rather than in an assertion. -/
def ascribeAssertionArgs (f : Term) (n : Nat) : DoElabM Term := do
  if n == 0 then return f
  let some pred ← assertionLanguage? | return f
  let mut tys := #[]
  let mut pred := pred
  for _ in *...n do
    let .forallE _ d b _ := pred | return f
    tys := tys.push (← Term.exprToSyntax d)
    pred := b
  `(($f : $(← tys.foldrM (init := ← `(_)) fun ty acc => `($ty → $acc))))

end Lean.Elab.Do
