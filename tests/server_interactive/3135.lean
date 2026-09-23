import Lean
/-!
# Loose docstrings
-/

open Lean Parser Command in
@[command_recover_parser]
def looseDocComment := leading_parser docComment

open Lean Elab Command in
@[command_elab looseDocComment] def elabLooseDocComment : CommandElab := fun _ => do
  logError m!"Unexpected doc string. Doc strings must come immediately before declarations that accept them.\n\n\
     Hint: `set_option ... in` must come before docstrings."

/-!
Basic test
-/

section
/-- This is a loose docstring -/
--^ collectDiagnostics
end

section
/-- This is a loose docstring before an 'in' command. -/
--^ collectDiagnostics
set_option pp.all true in
def x := 0

-- Still elaborates the `def`
#check x
     --^ textDocument/hover
end

section
set_option pp.all true in
/-- This is a docstring in its correct position. -/
def y := 0
end
