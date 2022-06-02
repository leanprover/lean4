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

open System
namespace Lake

/-- A Lake context with some additional caching for builds. -/
structure BuildContext extends Context where
  leanTrace : BuildTrace

/-- A transformer to equip a monad with a `BuildContext`. -/
abbrev BuildT := ReaderT BuildContext

/-- The monad for the Lake build manager. -/
abbrev SchedulerM := BuildT <| LogT BaseIO

/-- The monad for Lake builds. -/
abbrev BuildM := BuildT <| MonadLogT BaseIO OptionIO

/-- The `Task` monad for Lake builds. -/
abbrev BuildTask := OptionIOTask

instance : MonadError BuildM := ⟨MonadLog.error⟩
instance : MonadLift IO BuildM := ⟨MonadError.runIO⟩

instance [Pure m] : MonadLift LakeM (BuildT m) where
  monadLift x := fun ctx => pure <| x.run ctx.toContext

instance : MonadLift (LogT IO) BuildM where
  monadLift x := fun ctx meths => liftM (n := BuildM) (x.run meths.lift) ctx meths

def BuildM.run (logMethods : MonadLog BaseIO) (ctx : BuildContext) (self : BuildM α) : IO α :=
  self ctx logMethods |>.toIO fun _ => IO.userError "build failed"

def BuildM.catchFailure (f : Unit → BaseIO α) (self : BuildM α) : SchedulerM α :=
  fun ctx logMethods => self ctx logMethods |>.catchFailure f
