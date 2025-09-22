module
public import Lean

set_option linter.missingDocs true

/-- Docstring -/
syntax (name := test) "test" : tactic

@[tactic_alt test]
syntax "test1" : tactic

@[tactic_alt test]
macro "test2" : tactic => `(tactic| test1)

@[tactic_alt test]
elab "test2" : tactic => return ()
