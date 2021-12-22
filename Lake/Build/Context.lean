/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Task
import Lake.Config.Opaque
import Lake.Config.InstallPath
import Lake.Config.Context
import Lake.Build.Trace
import Lake.Build.IO

open System
namespace Lake

/-- A Lake context with some additional caching for builds. -/
structure BuildContext extends Context where
  leanTrace : BuildTrace

/-- The monad for Lake builds. -/
abbrev BuildM := ReaderT BuildContext BuildIO

/-- `Task` type for `BuildM`/`BuildIO`. -/
abbrev BuildTask := OptionIOTask

def BuildM.run (logMethods : LogMethods BaseIO) (ctx : BuildContext) (self : BuildM α) : IO α :=
  self ctx |>.run logMethods
