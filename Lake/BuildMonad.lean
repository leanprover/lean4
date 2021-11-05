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

/-- TODO: Replace with an `EIOTask PUnit` once Lean supports such a thing. -/
abbrev BuildTask := IOTask

namespace BuildTask

def spawn (act : BuildCoreM α) (prio := Task.Priority.dedicated) : BuildCoreM (BuildTask α) :=
  fun meths => BuildCoreM.runWith meths do IO.asTask (act.run meths) prio

instance : Async BuildCoreM BuildTask := ⟨spawn⟩

protected def await (self : BuildTask α) : BuildCoreM α := do
  match (← IO.wait self) with
  | Except.ok a    => pure a
  | Except.error e => logError (toString e); failure

instance : Await BuildTask BuildCoreM := ⟨BuildTask.await⟩

protected def mapAsync (f : α → BuildCoreM β) (self : BuildTask α) (prio := Task.Priority.dedicated) : BuildCoreM (BuildTask β) :=
  fun meths => BuildCoreM.runWith meths do self.mapAsync (fun a => f a |>.run meths) prio

instance : MapAsync BuildCoreM BuildTask := ⟨BuildTask.mapAsync⟩

protected def bindAsync (self : BuildTask α) (f : α → BuildCoreM (BuildTask β)) (prio := Task.Priority.dedicated) : BuildCoreM (BuildTask β) :=
  fun meths => BuildCoreM.runWith meths do self.bindAsync (fun a => f a |>.run meths) prio

instance : BindAsync BuildCoreM BuildTask := ⟨BuildTask.bindAsync⟩

protected def seqLeftAsync (self : BuildTask α) (act : BuildCoreM β) (prio := Task.Priority.dedicated) : BuildCoreM (BuildTask α) :=
  fun meths => BuildCoreM.runWith meths do self.seqLeftAsync (act.run meths) prio

instance : SeqLeftAsync BuildCoreM BuildTask := ⟨BuildTask.seqLeftAsync⟩

protected def seqRightAsync (self : BuildTask α) (act : BuildCoreM β) (prio := Task.Priority.dedicated) : BuildCoreM (BuildTask β) :=
  fun meths => BuildCoreM.runWith meths do self.seqRightAsync (act.run meths) prio

instance : SeqRightAsync BuildCoreM BuildTask := ⟨BuildTask.seqRightAsync⟩

end BuildTask
