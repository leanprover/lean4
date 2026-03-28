/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public meta import Lean.Elab.Command
public import Init.Notation
import Lean.Exception

/-!
# The `reprove` command

This command reproves a list of declarations with a given tactic sequence.
It is useful for testing tactics.
-/

public section

namespace Lean.Elab.Command

open Meta

/-- Reproving a declaration with a given tactic sequence -/
meta def reproveDecl (declName : Name) (tacticSeq : TSyntax `Lean.Parser.Tactic.tacticSeq) : CommandElabM Unit := do
  let some info := (← getEnv).find? declName
    | throwError "unknown declaration '{declName}'"

  let uniqueName ← liftCoreM <| mkFreshUserName `reprove_example

  let value ← liftTermElabM do
    Term.withDeclName uniqueName do
      let goal ← mkFreshExprMVar info.type
      let goalMVar := goal.mvarId!
      let _goals ← Tactic.run goalMVar do
        Tactic.evalTactic tacticSeq
      instantiateMVars goal

  let decl := Declaration.defnDecl {
    name := uniqueName
    type := info.type
    value := value
    levelParams := info.levelParams
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.safe
  }

  liftCoreM <| addAndCompile decl

/--
Reproves a list of declarations with a given tactic sequence.

```lean
reprove theorem1 theorem2 theorem3 by simp
```
-/
syntax (name := reprove) "reprove " ident+ " by " tacticSeq : command

@[command_elab «reprove»]
meta def elabReprove : CommandElab := fun stx => do
  let identStxs := stx[1].getArgs
  let tacticSeq : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨stx[3]⟩
  for identStx in identStxs do
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo identStx
    reproveDecl declName tacticSeq

end Lean.Elab.Command
