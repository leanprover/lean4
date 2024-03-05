/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
prelude
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Command
import Lean.Elab.Tactic.Meta
import Lean.Meta.CheckTactic

/-!
Commands to validate tactic results.
-/

namespace Lean.Elab.CheckTactic

open Lean.Meta CheckTactic
open Lean.Elab.Tactic
open Lean.Elab.Command

@[builtin_command_elab Lean.Parser.checkTactic]
def elabCheckTactic : CommandElab := fun stx => do
  let `(#check_tactic $t ~> $result by $tac) := stx | throwUnsupportedSyntax
  withoutModifyingEnv $ do
    runTermElabM $ fun _vars => do
      let u ← Lean.Elab.Term.elabTerm t none
      let type ← inferType u
      let checkGoalType ← mkCheckGoalType u type
      let mvar ← mkFreshExprMVar (.some checkGoalType)
      let expTerm ← Lean.Elab.Term.elabTerm result (.some type)
      let (goals, _) ← Lean.Elab.runTactic mvar.mvarId! tac.raw
      match goals with
      | [] =>
        throwError m!"{tac} closed goal, but is expected to reduce to {indentExpr expTerm}."
      | [next] => do
        let (val, _, _) ← matchCheckGoalType (←next.getType)
        if !(← Meta.withReducible <| isDefEq val expTerm) then
          throwError m!"Term reduces to{indentExpr val}\nbut is expected to reduce to {indentExpr expTerm}"
      | _ => do
        throwError m!"{tac} produced multiple goals, but is expected to reduce to {indentExpr expTerm}."

@[builtin_command_elab Lean.Parser.checkTacticFailure]
def elabCheckTacticFailure : CommandElab := fun stx => do
  let `(#check_tactic_failure $t by $tactic) := stx | throwUnsupportedSyntax
  withoutModifyingEnv $ do
    runTermElabM $ fun _vars => do
      let val ← Lean.Elab.Term.elabTerm t none
      let type ← inferType val
      let checkGoalType ← mkCheckGoalType val type
      let mvar ← mkFreshExprMVar (.some checkGoalType)
      let act := Lean.Elab.runTactic mvar.mvarId! tactic.raw
      match ← try (Term.withoutErrToSorry (some <$> act)) catch _ => pure none with
        | none =>
          pure ()
        | some (gls, _) =>
          let ppGoal (g : MVarId) := do
                let (val, _type, _u) ← matchCheckGoalType (← g.getType)
                pure m!"{indentExpr val}"
          let msg ←
            match gls with
              | [] => pure m!"{tactic} expected to fail on {t}, but closed goal."
              | [g] =>
                pure <| m!"{tactic} expected to fail on {t}, but returned: {←ppGoal g}"
              | gls =>
                let app m g := do pure <| m ++ (←ppGoal g)
                let init := m!"{tactic} expected to fail on {t}, but returned goals:"
                gls.foldlM (init := init) app
          throwError msg

@[builtin_macro Lean.Parser.checkSimp]
def expandCheckSimp : Macro := fun stx => do
  let `(#check_simp $t ~> $exp) := stx | Macro.throwUnsupported
  `(command|#check_tactic $t ~> $exp by simp)

@[builtin_macro Lean.Parser.checkSimpFailure]
def expandCheckSimpFailure : Macro := fun stx => do
  let `(#check_simp $t !~>) := stx | Macro.throwUnsupported
  `(command|#check_tactic_failure $t by simp)

end Lean.Elab.CheckTactic
