/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Tactic.Simp
import Lean.Meta.Tactic.TryThis

namespace Lean.Elab.Tactic

private def addConfigItem (stx : Syntax) (item : Syntax) : Syntax :=
  let optConfig := stx[1]
  let optConfig := optConfig.modifyArg 0 fun arg => mkNullNode (#[item] ++ arg.getArgs)
  stx.setArg 1 optConfig

set_option hygiene false in
private def addArith (stx : Syntax) : CoreM Syntax :=
  return addConfigItem stx (← `(Lean.Parser.Tactic.configItem| +arith))

set_option hygiene false in
private def addDecide (stx : Syntax) : CoreM Syntax :=
  return addConfigItem stx (← `(Lean.Parser.Tactic.configItem| +decide))

private def setKind (stx : Syntax) (str : String) (kind : SyntaxNodeKind) : Syntax :=
  let stx := stx.setKind kind
  stx.setArg 0 (mkAtom str)

private def addSuggestions (stx : Syntax) (tokenNew : String) (kindNew : SyntaxNodeKind) : MetaM Unit := do
  let stx' := setKind stx tokenNew kindNew
  let stx' := stx'.unsetTrailing
  let s₁ : TSyntax `tactic := ⟨← addArith stx'⟩
  let s₂ : TSyntax `tactic := ⟨← addArith (← addDecide stx')⟩
  Meta.Tactic.TryThis.addSuggestions stx[0] #[s₁, s₂] (origSpan? := (← getRef))

@[builtin_tactic Lean.Parser.Tactic.simpArith] def evalSimpArith : Tactic := fun stx => do
  addSuggestions stx "simp" ``Parser.Tactic.simp
  throwError "`simp_arith` has been deprecated. It was a shorthand for `simp +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented."

@[builtin_tactic Lean.Parser.Tactic.simpArithBang] def evalSimpArithBang : Tactic := fun stx => do
  addSuggestions stx "simp!" ``Parser.Tactic.simpAutoUnfold
  throwError "`simp_arith!` has been deprecated. It was a shorthand for `simp! +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented."

@[builtin_tactic Lean.Parser.Tactic.simpAllArith] def evalSimpAllArith : Tactic := fun stx => do
  addSuggestions stx "simp_all" ``Parser.Tactic.simpAll
  throwError "`simp_all_arith` has been deprecated. It was a shorthand for `simp_all +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented."

@[builtin_tactic Lean.Parser.Tactic.simpAllArithBang] def evalSimpAllArithBang : Tactic := fun stx => do
  addSuggestions stx "simp_all!" ``Parser.Tactic.simpAllAutoUnfold
  throwError "`simp_all_arith!` has been deprecated. It was a shorthand for `simp_all! +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented."


end Lean.Elab.Tactic
