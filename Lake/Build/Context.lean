/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Log
import Lake.Util.Task
import Lake.Util.Error
import Lake.Util.OptionIO
import Lake.Config.Context
import Lake.Build.Trace
import Lake.Build.Store
import Lake.Build.Topological

open System
namespace Lake

/-- The `Task` monad for Lake builds. -/
abbrev BuildTask := OptionIOTask

/-- A Lake build job. -/
abbrev Job := BuildTask BuildTrace

/-- A Lake context with some additional caching for builds. -/
structure BuildContext extends Context where
  leanTrace : BuildTrace

/-- A transformer to equip a monad with a `BuildContext`. -/
abbrev BuildT := ReaderT BuildContext

/-- The monad for the Lake build manager. -/
abbrev SchedulerM := BuildT <| LogT BaseIO

/-- The core monad for Lake builds. -/
abbrev BuildM := BuildT <| MonadLogT BaseIO OptionIO

/-- A transformer to equip a monad with a Lake build store. -/
abbrev BuildStoreT := StateT BuildStore

/-- A transformer for monads that may encounter a build cycle. -/
abbrev BuildCycleT := CycleT BuildKey

/-- A recursive build of a Lake build store that may encounter a cycle. -/
abbrev RecBuildM := BuildCycleT <| BuildStoreT BuildM

instance : MonadError BuildM := ⟨MonadLog.error⟩
instance : MonadLift IO BuildM := ⟨MonadError.runIO⟩

instance [Pure m] : MonadLift LakeM (BuildT m) where
  monadLift x := fun ctx => pure <| x.run ctx.toContext

instance : MonadLift LogIO BuildM where
  monadLift x := fun ctx meths => liftM (n := BuildM) (x.run meths.lift) ctx meths

def BuildM.run (logMethods : MonadLog BaseIO) (ctx : BuildContext) (self : BuildM α) : IO α :=
  self ctx logMethods |>.toIO fun _ => IO.userError "build failed"

def BuildM.catchFailure (f : Unit → BaseIO α) (self : BuildM α) : SchedulerM α :=
  fun ctx logMethods => self ctx logMethods |>.catchFailure f
