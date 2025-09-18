/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.Elab.Command
import Lean.Elab.Tactic.Basic
import Lean.Elab.Term

/-!
# The `reprove` command

This command reproves a list of declarations with a given tactic sequence.
It is useful for testing tactics.
-/

public section

namespace Lean.Elab.Command

open Meta

/-- Reproving a declaration with a given tactic sequence -/
def reproveDecl (declName : Name) (tacticSeq : TSyntax `Lean.Parser.Tactic.tacticSeq) : CommandElabM Unit := do
  let some info := (← getEnv).find? declName
    | throwError "unknown declaration '{declName}'"

  let typeStx ← liftTermElabM <| PrettyPrinter.delab info.type
  elabCommand (← `(command| example : $typeStx := by $tacticSeq))

/--
Reproves a list of declarations with a given tactic sequence.

```lean
reprove theorem1 theorem2 theorem3 by simp
```
-/
syntax (name := reprove) "reprove " ident+ " by " tacticSeq : command

@[command_elab «reprove»]
def elabReprove : CommandElab := fun stx => do
  let declNames := stx[1].getArgs.map (·.getId)
  let tacticSeq : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨stx[3]⟩
  for declName in declNames do
    reproveDecl declName tacticSeq

end Lean.Elab.Command
