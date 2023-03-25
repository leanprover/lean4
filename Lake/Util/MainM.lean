/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Log
import Lake.Util.Exit
import Lake.Util.Error
import Lake.Util.Lift

namespace Lake

/--
The monad in Lake for `main`-like functions.
Supports IO, logging, and `exit`.
-/
def MainM := EIO ExitCode

instance : Monad MainM := inferInstanceAs (Monad (EIO ExitCode))
instance : MonadFinally MainM := inferInstanceAs (MonadFinally (EIO ExitCode))
instance : MonadLift BaseIO MainM := inferInstanceAs (MonadLift BaseIO (EIO ExitCode))

namespace MainM

/-! # Basics -/

@[inline] protected def mk (x : EIO ExitCode α) : MainM α :=
  x

@[inline] protected def toEIO (self : MainM α) : EIO ExitCode α :=
  self

@[inline] protected def toBaseIO (self : MainM α) : BaseIO (Except ExitCode α) :=
  self.toEIO.toBaseIO

protected def run (self : MainM α) : BaseIO ExitCode :=
  self.toBaseIO.map fun | Except.ok _ => 0 | Except.error rc => rc

/-! # Exits -/

/-- Exit with given return code. -/
protected def exit (rc : ExitCode) : MainM α :=
  MainM.mk <| throw rc

instance : MonadExit MainM := ⟨MainM.exit⟩

/-- Try this and catch exits. -/
protected def tryCatchExit (f : ExitCode → MainM α) (self : MainM α) : MainM α :=
  self.toEIO.tryCatch f

/-- Try this and catch error codes (i.e., non-zero exits). -/
protected def tryCatchError (f : ExitCode → MainM α) (self : MainM α) : MainM α :=
  self.tryCatchExit fun rc => if rc = 0 then exit 0 else f rc

/-- Exit with a generic error code (i.e., 1). -/
protected def failure : MainM α :=
  exit 1

/-- If this exits with an error code (i.e., not 0), perform other. -/
protected def orElse (self : MainM α) (other : Unit → MainM α) : MainM α :=
  self.tryCatchExit fun rc => if rc = 0 then exit 0 else other ()

instance : Alternative MainM where
  failure := MainM.failure
  orElse := MainM.orElse

/-! # Logging and IO -/

instance : MonadLog MainM := MonadLog.eio

/-- Print out a error line with the given message and then exit with an error code. -/
protected def error (msg : String) (rc : ExitCode := 1) : MainM α := do
  logError msg
  exit rc

instance : MonadError MainM := ⟨MainM.error⟩
instance : MonadLift IO MainM := ⟨MonadError.runEIO⟩

def runLogIO (x : LogIO α) (verbosity := Verbosity.normal) : MainM α :=
  liftM <| x.run <| MonadLog.eio verbosity

instance : MonadLift LogIO MainM := ⟨runLogIO⟩
