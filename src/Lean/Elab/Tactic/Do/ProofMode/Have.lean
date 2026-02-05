/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.Syntax
public import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Do.ProofMode.Focus
import Lean.Elab.Tactic.ElabTerm

public section

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do SPred.Tactic
open Lean Elab Tactic Meta

@[builtin_tactic Lean.Parser.Tactic.mdup]
def elabMDup : Tactic
  | `(tactic| mdup $h:ident => $h₂:ident) => do
    let (mvar, goal) ← ensureMGoal
    mvar.withContext do
    let some res := goal.focusHyp h.raw.getId | throwError m!"Hypothesis {h} not found"
    let P := goal.hyps
    let Q := res.restHyps
    let H := res.focusHyp
    let uniq ← mkFreshId
    let hyp := Hyp.mk h₂.raw.getId uniq H.consumeMData
    addHypInfo h goal.σs hyp (isBinder := true)
    let H' := hyp.toExpr
    let T := goal.target
    let newGoal := { goal with hyps := SPred.mkAnd! goal.u goal.σs P H' }
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    mvar.assign (mkApp7 (mkConst ``Have.dup [goal.u]) goal.σs P Q H T res.proof m)
    replaceMainGoal [m.mvarId!]
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.mhave]
def elabMHave : Tactic
  | `(tactic| mhave $h $[: $ty?]? := $rhs) => do
    let (mvar, goal) ← ensureMGoal
    mvar.withContext do
    -- build goal `P ⊢ₛ T` from `P ⊢ₛ H` and residual goal `P ∧ H ⊢ₛ T`
    let P := goal.hyps
    let spred := mkApp (mkConst ``SPred [goal.u]) goal.σs
    let H ← match ty? with
      | some ty => elabTerm ty spred
      | _       => mkFreshExprMVar spred
    let uniq ← mkFreshId
    let hyp := Hyp.mk h.raw.getId uniq H
    addHypInfo h goal.σs hyp (isBinder := true)
    let H := hyp.toExpr
    let T := goal.target
    let (PH, hand) := SPred.mkAnd goal.u goal.σs P H
    let haveGoal := { goal with target := H }
    let hhave ← elabTermEnsuringType rhs haveGoal.toExpr
    let newGoal := { goal with hyps := PH }
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    mvar.assign (mkApp8 (mkConst ``Have.have [goal.u]) goal.σs P H PH T hand hhave m)
    replaceMainGoal [m.mvarId!]
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.mreplace]
def elabMReplace : Tactic
  | `(tactic| mreplace $h $[: $ty?]? := $rhs) => do
    let (mvar, goal) ← ensureMGoal
    mvar.withContext do
    -- build goal `P ⊢ₛ T` from `P ⊢ₛ H` and residual goal `P ∧ H ⊢ₛ T`
    let PH := goal.hyps
    let some res := goal.focusHyp h.raw.getId | throwError m!"Hypothesis {h} not found"
    let P := res.restHyps
    let H := res.focusHyp
    let spred := mkApp (mkConst ``SPred [goal.u]) goal.σs
    let H' ← match ty? with
      | some ty => elabTerm ty spred
      | _       => mkFreshExprMVar spred
    let uniq ← mkFreshId
    let hyp := Hyp.mk h.raw.getId uniq H'
    addHypInfo h goal.σs hyp (isBinder := true)
    let H' := hyp.toExpr
    let haveGoal := { goal with target := H' }
    let hhave ← elabTermEnsuringType rhs haveGoal.toExpr
    let T := goal.target
    let (PH', hand) := SPred.mkAnd goal.u goal.σs P H'
    let newGoal := { goal with hyps := PH' }
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    let prf := mkApp (mkApp10 (mkConst ``Have.replace [goal.u]) goal.σs P H H' PH PH' T res.proof hand hhave) m
    mvar.assign prf
    replaceMainGoal [m.mvarId!]
  | _ => throwUnsupportedSyntax
