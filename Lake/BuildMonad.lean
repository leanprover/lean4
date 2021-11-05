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

abbrev BuildCoreM := LogMethodsT BaseIO <| EIO PUnit
abbrev BuildM := ReaderT BuildContext BuildCoreM

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

namespace BuildCoreM

def run (logMethods : LogMethods BaseIO) (self : BuildCoreM α) : IO α :=
  ReaderT.run self logMethods |>.toIO fun _ => IO.userError "build failed"

def runWith (logMethods : LogMethods BaseIO) (self : BuildCoreM α) : EIO PUnit α :=
  ReaderT.run self logMethods

protected def failure : BuildCoreM α :=
  throw ()

protected def orElse (self : BuildCoreM α) (f : Unit → BuildCoreM α) : BuildCoreM α :=
  tryCatch self f

instance : Alternative BuildCoreM where
  failure := BuildCoreM.failure
  orElse := BuildCoreM.orElse

def runIO (x : IO α) : BuildCoreM α := do
  match (← x.toBaseIO) with
  | Except.ok a => pure a
  | Except.error e => do
    logError (toString e)
    failure

instance : MonadLift IO BuildCoreM := ⟨runIO⟩

instance : MonadLift (LogT IO) BuildCoreM where
  monadLift x := fun meths => runIO (x.run meths.lift) meths

end BuildCoreM

def BuildM.run (logMethods : LogMethods BaseIO) (ctx : BuildContext) (self : BuildM α) : IO α :=
  self ctx |>.run logMethods

def failOnBuildCycle [ToString k] : Except (List k) α → BuildM α
| Except.ok a => a
| Except.error cycle => do
  let cycle := cycle.map (s!"  {·}")
  logError s!"build cycle detected:\n{"\n".intercalate cycle}"
  failure

/-- `Task` type for `BuildM`/`BuildCoreM`. -/
abbrev BuildTask := EIOTask PUnit
