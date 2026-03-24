/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Mario Carneiro, Kim Morrison
-/
module

prelude
public import Lean.Meta.Tactic.Symm
public import Lean.Elab.Tactic.Location

public section

namespace Lean.Elab.Tactic

open Meta

@[builtin_tactic Lean.Parser.Tactic.symm]
def evalSymm : Tactic := fun stx =>
  match stx with
  | `(tactic| symm $(loc?)?) => do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc?))
      (atLocal := fun h => liftMetaTactic1 fun g => g.applySymmAt h)
      (atTarget := liftMetaTactic1 fun g => g.applySymm)
      (throwTacticEx `symm · "`symm` made no progress")
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.symmSaturate]
def evalSymmSaturate : Tactic := fun stx =>
  match stx with
  | `(tactic| symm_saturate) => do
    liftMetaTactic1 fun g => g.symmSaturate
  | _ => throwUnsupportedSyntax
