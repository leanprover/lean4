/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Lean.Elab.Tactic.Grind.Config
import Lean.Meta.Tactic.Grind.Main
import Lean.Meta.Tactic.Grind.NormSym
namespace Lean.Elab.Tactic
open Meta

/-!
The `grind_norm` tactic is a debugging aid for the migration of the `grind` normalizer to
`Sym.simp`. It will be deleted once the migration is complete.
-/

/-- Which normalizer `grind_norm` runs. -/
inductive NormMode where
  /-- The legacy `simp`-based normalizer. -/
  | legacy
  /-- The `Sym.simp`-based normalizer. -/
  | sym
  /-- Both, failing if the results differ. -/
  | check

@[builtin_tactic Lean.Parser.Tactic.grindNorm] def evalGrindNorm : Tactic := fun stx => withMainContext do
  let config ← elabGrindConfig stx[1]
  let mode : NormMode := match stx[2].getOptional? with
    | none => .legacy
    | some s => if s[0].getAtomVal == "sym" then .sym else .check
  let mvarId ← getMainGoal
  let target ← instantiateMVars (← mvarId.getType)
  let params ← Meta.Grind.mkDefaultParams config
  let r ← Meta.Grind.GrindM.run (params := params) <| Meta.Grind.withGTransparency do
    match mode with
    | .legacy => Meta.Grind.normLegacy target
    | .sym => Meta.Grind.normSym target
    | .check =>
      let r₁ ← Meta.Grind.normLegacy target
      let r₂ ← Meta.Grind.normSym target
      -- `shareCommon` restores the `Sym` invariants (reducible constants unfolded, kernel
      -- projections folded) on the legacy result too, so the comparison is fair.
      let e₁ ← Sym.shareCommon r₁.expr
      let e₂ ← Sym.shareCommon r₂.expr
      unless Sym.isSameExpr e₁ e₂ do
        throwError "`grind_norm` discrepancy\nlegacy:{indentExpr e₁}\nsym:{indentExpr e₂}"
      return r₁
  let mvarId' ← applySimpResultToTarget mvarId target r
  replaceMainGoal [mvarId']

end Lean.Elab.Tactic
