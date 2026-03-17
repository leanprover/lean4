import Lean
import LeanChecker.Replay

-- Test: Quot/Eq dependency ordering
--
-- Test that `replay` correctly handles the dependency of `Quot` on `Eq`.
-- `Quot.lift` and `Quot.ind` have types that reference `Eq`, so when replaying
-- a minimal set of constants that includes `Quot` (via `Quot.sound`), we need
-- to ensure `Eq` is added to the kernel environment before `quotDecl`.
--
-- See https://github.com/leanprover/comparator/issues/1

open Lean

-- Test replaying a minimal set of constants including Quot from a fresh environment.
-- This exercises the fix for the Quot/Eq dependency ordering issue.
#eval show IO Unit from do
  -- Get the current environment which has all the constants we need
  let env ← importModules #[{ module := `Init }] {}

  -- Build a minimal constant map with just Quot.sound, Eq, and their direct requirements
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for name in [`Quot.sound, `Eq, `Eq.refl, `Quot] do
    if let some ci := env.find? name then
      constants := constants.insert name ci

  IO.println s!"Constants to replay: {constants.size}"

  -- Replay from a fresh environment - this would fail before the fix
  -- if Quot was processed before Eq
  let freshEnv ← mkEmptyEnvironment
  let _ ← freshEnv.replay' constants

  IO.println "Replay succeeded!"
