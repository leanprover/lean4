import Lean

open Lean
def oh_no : Nat := 0

def snakeLinter : Linter := fun stx => do
  if stx.getKind == `Lean.Parser.Command.declaration then
    let decl := stx[1]
    if decl.getKind == `Lean.Parser.Command.def then
      let declId   := decl[1]
      withRef declId do
        let declName := declId[0].getId
        if declName.eraseMacroScopes.toString.contains '_' then
          -- TODO(Sebastian): return actual message with position from syntax tree
          throwError "SNAKES!!"

initialize addLinter snakeLinter
