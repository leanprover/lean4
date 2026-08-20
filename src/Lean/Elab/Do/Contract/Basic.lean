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

/-- Synthesize the `Std.WP.WPMonad` dictionary of the `do` block's monad, and return the assertion
type that its `outParam` determines: `StateM Nat` gives `Nat → Prop`. -/
def assertionLanguage? : DoElabM (Option Expr) := do
  let wpMonad := `Std.WP.WPMonad
  unless (← getEnv).contains wpMonad do return none
  let wpTy ← Term.elabType <| ←
    `($(mkIdent wpMonad) $(← Term.exprToSyntax (← read).monadInfo.m) _ _)
  let .some _ ← trySynthInstance wpTy | return none
  let some pred := wpTy.getAppArgs[1]? | return none
  let pred ← instantiateMVars pred
  return if pred.hasExprMVar then none else some pred

/-- Ascribe the first `n` argument types of the assertion language to `f`, after `numLeading` holes
for the binders a clause states first. In `StateM (Nat × Nat)`, `f = fun ⟨lo, hi⟩ => lo ≤ hi` and
`n = 1` give `(fun ⟨lo, hi⟩ => lo ≤ hi : Nat × Nat → _)`. The result stays a hole, because a
`decreasing` measure ends in the measure type. -/
def ascribeAssertionArgs (f : Term) (n : Nat) (numLeading : Nat := 0) : DoElabM Term := do
  if n == 0 && numLeading == 0 then return f
  let some pred ← assertionLanguage? | return f
  let mut tys := #[]
  for _ in *...numLeading do
    tys := tys.push (← `(_))
  let mut pred := pred
  for _ in *...n do
    let .forallE _ d b _ := pred | return f
    tys := tys.push (← Term.exprToSyntax d)
    pred := b
  `(($f : $(← tys.foldrM (init := ← `(_)) fun ty acc => `($ty → $acc))))

end Lean.Elab.Do
