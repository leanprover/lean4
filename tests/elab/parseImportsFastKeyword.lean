module

meta import Lean.Elab.Import
meta import Lean.Elab.ParseImportsFast

/-! Regression test for #16307: the fast import parser must match whole keywords. -/

open Lean

#eval show IO Unit from do
  for input in #[
    "module\nimport allValues", "import allValues", "module\nimport all₁",
    "module\nimport all.Values", "module\nimport all.«some name»",
    "module\nimport all Values", "module\nimport all/- comment -/Values", "importFoo"
  ] do
    let (expected, _, msgs) ← Elab.parseImports input
    if msgs.hasErrors then throw <| IO.userError s!"invalid test header: {input}"
    let header ← parseImports' input "<test>"
    unless header.imports == expected do
      throw <| IO.userError s!"{input}: expected {expected}, got {header.imports}"
