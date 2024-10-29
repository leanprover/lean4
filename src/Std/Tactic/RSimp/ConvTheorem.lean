/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Std.Tactic.RSimp.Setup
import Lean.Elab.Tactic
import Lean.Elab.DeclUtil
import Lean.Elab.Command
import Lean.Elab.Tactic.Conv
import Init.Tactics
import Init.Conv

open Lean.Parser in
/--
Abstracts the right-hand side into its own constant of the given name, and
uses it in the `conv_theorem`.
-/
def namedRhs := leading_parser
  atomic (" (" >> nonReservedSymbol "abstract_rhs") >> " := " >> ident >> ")"

open Lean.Parser.Tactic in
/--
TODO
-/
syntax (name := convTheorem) declModifiers "conv_theorem" (namedRhs)? declId declSig " => " Conv.convSeq : command


open Lean Meta Elab Command Tactic

def convert (lhs : Expr) (conv : TacticM Unit) : TermElabM (Expr × Expr) := do
  let (rhs, newGoal) ← Conv.mkConvGoalFor lhs
  let _ ← Tactic.run newGoal.mvarId! do
    conv
    for mvarId in (← getGoals) do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    pruneSolvedGoals
    unless (← getGoals).isEmpty do
      throwError "convert tactic failed, there are unsolved goals\n{goalsToMessageData (← getGoals)}"
  return (← instantiateMVars rhs, ← instantiateMVars newGoal)

@[command_elab convTheorem]
def elabConvTheorem : CommandElab := fun stx => do
  let modifiers ← elabModifiers ⟨stx[0]⟩
  let declId             := stx[3]
  let (binders, lhsStx) := expandDeclSig stx[4]
  let scopeLevelNames ← getLevelNames
  let ⟨_, declName, allUserLevelNames⟩ ← expandDeclId declId modifiers
  addDeclarationRanges declName modifiers.stx stx
  runTermElabM fun vars =>
    Term.withDeclName declName <| Term.withLevelNames allUserLevelNames <| Term.elabBinders binders.getArgs fun xs => do
      Term.applyAttributesAt declName modifiers.attrs AttributeApplicationTime.beforeElaboration
      let lhs ← Term.elabTerm lhsStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let lhs ← instantiateMVars lhs
      let (rhs, value) ← convert lhs (Tactic.evalTactic stx[6])
      let type ← mkEq lhs rhs
      let type ← mkForallFVars xs type
      let type ← mkForallFVars vars type
      let type ← Term.levelMVarToParam type
      let value ← mkLambdaFVars xs value
      let value ← mkLambdaFVars vars value
      let usedParams  := collectLevelParams {} type |>.params
      match sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams with
      | Except.error msg      => throwErrorAt stx msg
      | Except.ok levelParams =>
        let type ← instantiateMVars type
        let value ← instantiateMVars value
        let decl := Declaration.thmDecl {
          name        := declName,
          levelParams := levelParams,
          type        := type,
          value       := value,
        }
        Term.ensureNoUnassignedMVars decl
        addDecl decl
        withSaveInfoContext do  -- save new env
          Term.addTermInfo' declId (← mkConstWithLevelParams declName) (isBinder := true)
        Term.applyAttributesAt declName modifiers.attrs AttributeApplicationTime.afterTypeChecking
        Term.applyAttributesAt declName modifiers.attrs AttributeApplicationTime.afterCompilation



conv_theorem test : id 1 + 2 =>
  skip
  unfold id
  simp


#check test

conv_theorem test2  (a b c : Fin 12) : (a + b + c).val =>
  skip
  simp [Fin.ext_iff, Fin.val_add]

#check test2

-- test2 (a b c : Fin 12) : ↑(a + b + c) = test2_rhs_aux a b c
