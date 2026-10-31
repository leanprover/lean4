import Lean

/-!
Prints, for each module named on the command line, the code quality entries persisted into its
`.olean`, in order, as `<linter option>/<entry name>` with `_` for unattributed entries. Run via
`lake env lean --run PrintEntries.lean <modules>` from `run_test.sh` after building the package.
-/

open Lean Linter

def main (mods : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun mod => { module := mod.toName }) {}
  for (mod, entries) in getAllCodeQualityEntries env do
    unless entries.isEmpty do
      let described := entries.map fun e => s!"{(e.linter?.map toString).getD "_"}/{e.entry.name}"
      IO.println s!"{mod}: [{", ".intercalate described.toList}]"
