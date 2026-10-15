import Lean

/-!
`saveModuleData` stores arbitrary objects as is: `Batteries.Util.Pickle` and the REPL cast values
that are not `ModuleData` to it in order to pickle them, so it must not inspect its argument.
-/

open Lean

unsafe def pickleRoundtrip : IO Unit := do
  let path : System.FilePath := "_tmp_saveModuleDataPickle.olean"
  let x : Array Import × Nat := (#[{ module := `Init }, { module := `Lean }], 42)
  saveModuleData path `saveModuleDataPickle (unsafeCast x)
  let (y, region) ← readModuleData path
  let y : Array Import × Nat := unsafeCast y
  IO.println s!"{y.1.map (·.module)} {y.2}"
  region.free
  IO.FS.removeFile path

/-- info: #[Init, Lean] 42 -/
#guard_msgs in
#eval pickleRoundtrip
