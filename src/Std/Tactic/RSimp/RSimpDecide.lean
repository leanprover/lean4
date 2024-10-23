/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Std.Tactic.RSimp.Setup
import Lean.Elab.Tactic
import Init.Tactics

open Lean Elab Tactic Meta

private def preprocessPropToDecide (expectedType : Expr) : TermElabM Expr := do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then
    expectedType ← zetaReduce expectedType
  if expectedType.hasFVar || expectedType.hasMVar then
    throwError "expected type must not contain free or meta variables{indentExpr expectedType}"
  return expectedType

theorem of_opt_decide_eq_true {p : Prop} [inst : Decidable p] (c : Bool) (h : decide p = c)
  : c = true → p := by subst h; exact of_decide_eq_true

initialize registerTraceClass `tactic.rsimp_decide
initialize registerTraceClass `tactic.rsimp_decide.debug

section Syntax
open Lean.Parser.Tactic

/--
TODO
-/
syntax (name := rsimp_decide) "rsimp_decide" (config)? (discharger)?
    (&" only")? (" [" (simpErase <|> simpLemma),* "]")?  : tactic

@[tactic rsimp_decide]
def rsimpDecideImpl : Tactic := fun stx => do
  -- TODO: Using closeMainGoalUsing did not work as expected
  -- closeMainGoalUsing `rsimp_decide fun expectedType _tag => do
  withMainContext do
    let expectedType ← getMainTarget
    let expectedType ← preprocessPropToDecide expectedType
    let d ← mkAppOptM ``Decidable.decide #[expectedType, none]
    let d ← instantiateMVars d
    -- Get instance from `d`
    let s := d.appArg!
    let decE := mkApp2 (mkConst ``Decidable.decide) expectedType s
    let .some se ← getSimpExtension? `rsimp | throwError "simp set 'rsimp' not found"

    -- Setting up the simplifier
    -- Passing the stx here is a hairy hack, and only works as long as `rsimp_decide` syntax
    -- is compatible with the simp syntax. Maybe mkSimpContext should take the components
    -- separately
    let scr ← mkSimpContext stx
      (simpTheorems := se.getTheorems) (ignoreStarArg := true) (eraseLocal := false)
    let (res, _stats) ← scr.dischargeWrapper.with fun discharge? =>
      simp decE scr.ctx scr.simprocs discharge?

    let optE := res.expr
    trace[tactic.rsimp_decide] "Optimized expression:{indentExpr optE}"
    let optPrf ← res.getProof
    let rflPrf ← mkEqRefl (toExpr true)
    let rflType ← mkEq optE (toExpr true)
    -- We peform the kernel computation in an auxillary definition, like `decide!`
    let levelsInType := (collectLevelParams {} expectedType).params
    let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
    let lemmaName ←
      try
        mkAuxLemma [] rflType rflPrf
      catch e =>
        trace[tactic.rsimp_decide.debug] "mkAuxLemma failed: {e.toMessageData}"
        throwTacticEx `rsimp_decide (← getMainGoal) "this may be because the proposition is false, involves non-computable axioms or opaque definitions."
    let eqPrf := mkConst lemmaName (lemmaLevels.map .param)
    closeMainGoal `rsimp_decide <|
      mkApp5 (Lean.mkConst ``of_opt_decide_eq_true) expectedType s optE optPrf eqPrf


end Syntax
