/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Task
import Lake.Trace
import Lake.LogMonad
import Lake.InstallPath

open System
namespace Lake

--------------------------------------------------------------------------------
-- # Build Monad Definition
--------------------------------------------------------------------------------

structure BuildContext where
  leanTrace : BuildTrace
  leanInstall : LeanInstall
  lakeInstall : LakeInstall
  deriving Inhabited

abbrev BuildM := ReaderT BuildContext <| LogT <| IO

--------------------------------------------------------------------------------
-- # Build Monad Utilities
--------------------------------------------------------------------------------

def getLeanInstall : BuildM LeanInstall :=
  (·.leanInstall) <$> read

def getLeanIncludeDir : BuildM FilePath :=
  (·.includeDir) <$> getLeanInstall

def getLean : BuildM FilePath :=
  (·.lean) <$> getLeanInstall

def getLeanTrace : BuildM BuildTrace := do
  (·.leanTrace) <$> read

def getLeanc : BuildM FilePath :=
  (·.leanc) <$> getLeanInstall

def getLakeInstall : BuildM LakeInstall :=
  (·.lakeInstall) <$> read

namespace BuildM

def convErrors (self : BuildM α) : BuildM α := do
  try self catch e =>
    /-
      Remark: Actual error should have already been logged earlier.
      However, if the error was thrown by something that did not know it was
      in `BuildM` (e.g., a general `Target`), it may have not been.

      TODO: Use an `OptionT` in `BuildM` to properly record build failures.
    -/
    logError s!"build error: {toString e}"
    throw <| IO.userError "build failed"

def run (logMethods : LogMethods IO) (ctx : BuildContext) (self : BuildM α) : IO α :=
  (convErrors self) ctx logMethods

end BuildM

def failOnBuildCycle [ToString k] : Except (List k) α → BuildM α
| Except.ok a => a
| Except.error cycle => do
  let cycle := cycle.map (s!"  {·}")
  let msg := s!"build cycle detected:\n{"\n".intercalate cycle}"
  logError msg
  throw <| IO.userError msg

abbrev BuildTask := IOTask

instance : HAndThen (BuildTask α) (BuildM β) (BuildM (BuildTask β)) :=
  ⟨fun x y => seqRightAsync x (y ())⟩
