/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Mario Carneiro, Kim Morrison
-/
prelude
import Lean.Meta.Tactic.Symm
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic

@[builtin_tactic Lean.Parser.Tactic.symm]
def evalSymm : Tactic := fun stx =>
  match stx with
  | `(tactic| symm $(loc?)?) => do
    let atHyp h := liftMetaTactic1 fun g => g.applySymmAt h
    let atTarget := liftMetaTactic1 fun g => g.applySymm
    let loc := if let some loc := loc? then expandLocation loc else Location.targets #[] true
    withLocation loc atHyp atTarget fun _ => throwError "symm made no progress"
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.symmSaturate]
def evalSymmSaturate : Tactic := fun stx =>
  match stx with
  | `(tactic| symm_saturate) => do
    liftMetaTactic1 fun g => g.symmSaturate
  | _ => throwUnsupportedSyntax
