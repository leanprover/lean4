/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Elab.Tactic.Lets
import Lean.Elab.Tactic.Conv.Basic

/-!
# Conv tactics to manipulate `let` expressions
-/

open Lean Meta

namespace Lean.Elab.Tactic.Conv

@[builtin_tactic Lean.Parser.Tactic.Conv.extractLets] elab_rules : tactic
  | `(conv| extract_lets $cfg:optConfig $ids* $[$ellipsis?:ellipsis]?) => do
    let mut config ← elabExtractLetsConfig cfg
    if ellipsis?.isSome || ids.isEmpty then
      config := { config with onlyGivenNames := false }
    let givenNames := (ids.map getNameOfIdent').toList
    let (lhs, rhs) ← getLhsRhs
    let fvars ← liftMetaTacticAux fun mvarId => do
      mvarId.checkNotAssigned `extract_lets
      Meta.extractLets #[lhs] givenNames (config := config) fun fvarIds es => do
        let lhs' := es[0]!
        if fvarIds.isEmpty && lhs == lhs' then
          throwTacticEx `extract_lets mvarId m!"made no progress"
        let (rhs', g) ← mkConvGoalFor lhs' (← mvarId.getTag)
        let fvars := fvarIds.map .fvar
        let assign (mvar : MVarId) (e : Expr) : MetaM Unit := do
          let e ← mkLetFVars (usedLetOnly := false) fvars e
          mvar.withContext do
            unless ← isDefEq (.mvar mvar) e do
              throwTacticEx `extract_lets mvarId m!"(internal error) non-defeq in assignment"
            mvar.assign e
        assign rhs'.mvarId! rhs
        assign mvarId g
        return (fvarIds, [g.mvarId!])
    withMainContext do
      for stx in ids, fvar in fvars do
        Term.addLocalVarInfo stx (.fvar fvar)

@[builtin_tactic Lean.Parser.Tactic.Conv.liftLets] elab_rules : tactic
  | `(conv| lift_lets $cfg:optConfig) => do
    let mut config ← elabLiftLetsConfig cfg
    withMainContext do
      let lhs ← getLhs
      let lhs' ← Meta.liftLets lhs config
      if lhs == lhs' then
        throwTacticEx `lift_lets (← getMainGoal) m!"made no progress"
      changeLhs lhs'

end Lean.Elab.Tactic.Conv
