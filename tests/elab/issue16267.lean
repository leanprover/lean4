import Lean.Environment
open Lean

/-!
Regression test for #16267: `findOLean`'s package root cache must not keep names that live in the
`.olean` regions freed by `withImportModules`.
-/

unsafe def importTwice : IO Unit := do
  -- A new search path empties the cache, so the roots cached during the first import (`Init`,
  -- reached through `Lean.Data.Json`'s imports) are names from the regions freed afterwards.
  searchPathRef.modify (· ++ [System.FilePath.mk "_tmp_issue16267"])
  for i in [0:2] do
    withImportModules #[{ module := `Lean.Data.Json }] {} fun env =>
      IO.println s!"import {i}: {(env.find? `Lean.Json.compress).isSome}"

/--
info: import 0: true
import 1: true
-/
#guard_msgs in
#eval importTwice
