/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.LogT

namespace Lake

abbrev BuildCoreM :=
  LogMethodsT BaseIO <| EIO PUnit

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
