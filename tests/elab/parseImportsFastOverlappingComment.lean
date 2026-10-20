import Lean.Elab.ParseImportsFast

/-!
Regression test for overlapping block comment terminators in the fast import parser.
-/

open Lean

#eval do
  let header ← parseImports' "/- --/ import Foo.Bar\n" "<test>"
  unless header.imports.any (·.module == `Foo.Bar) do
    throw <| IO.userError "unexpected imports"
