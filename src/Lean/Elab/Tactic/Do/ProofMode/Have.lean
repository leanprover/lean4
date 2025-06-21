/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.Cases
import Lean.Elab.Tactic.Do.ProofMode.Specialize

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do
open Lean Elab Tactic Meta

def Have.dup {σs : List Type} {P Q H T : SPred σs} (hfoc : P ⊣⊢ₛ Q ∧ H) (hgoal : P ∧ H ⊢ₛ T) : P ⊢ₛ T :=
  (SPred.and_intro .rfl (hfoc.mp.trans SPred.and_elim_r)).trans hgoal

def Have.have {σs : List Type} {P H PH T : SPred σs} (hand : P ∧ H ⊣⊢ₛ PH) (hhave : P ⊢ₛ H) (hgoal : PH ⊢ₛ T) : P ⊢ₛ T :=
  (SPred.and_intro .rfl hhave).trans (hand.mp.trans hgoal)

def Have.replace {σs : List Type} {P H H' PH PH' T : SPred σs} (hfoc : PH ⊣⊢ₛ P ∧ H ) (hand : P ∧ H' ⊣⊢ₛ PH') (hhave : PH ⊢ₛ H') (hgoal : PH' ⊢ₛ T) : PH ⊢ₛ T :=
  (SPred.and_intro (hfoc.mp.trans SPred.and_elim_l) hhave).trans (hand.mp.trans hgoal)

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
  let newGoal := { goal with hyps := mkAnd! goal.σs P H' }
  let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  mvar.assign (mkApp7 (mkConst ``Have.dup) goal.σs P Q H T res.proof m)
  replaceMainGoal [m.mvarId!]
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.mhave]
def elabMHave : Tactic
  | `(tactic| mhave $h $[: $ty?]? := $rhs) => do
  let (mvar, goal) ← ensureMGoal
  mvar.withContext do
  -- build goal `P ⊢ₛ T` from `P ⊢ₛ H` and residual goal `P ∧ H ⊢ₛ T`
  let P := goal.hyps
  let spred := mkApp (mkConst ``SPred) goal.σs
  let H ← match ty? with
    | some ty => elabTerm ty spred
    | _       => mkFreshExprMVar spred
  let uniq ← mkFreshId
  let hyp := Hyp.mk h.raw.getId uniq H
  addHypInfo h goal.σs hyp (isBinder := true)
  let H := hyp.toExpr
  let T := goal.target
  let (PH, hand) := mkAnd goal.σs P H
  let haveGoal := { goal with target := H }
  let hhave ← elabTermEnsuringType rhs haveGoal.toExpr
  let newGoal := { goal with hyps := PH }
  let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  mvar.assign (mkApp8 (mkConst ``Have.have) goal.σs P H PH T hand hhave m)
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
  let spred := mkApp (mkConst ``SPred) goal.σs
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
  let (PH', hand) := mkAnd goal.σs P H'
  let newGoal := { goal with hyps := PH' }
  let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  let prf := mkApp (mkApp10 (mkConst ``Have.replace) goal.σs P H H' PH PH' T res.proof hand hhave) m
  mvar.assign prf
  replaceMainGoal [m.mvarId!]
  | _ => throwUnsupportedSyntax
