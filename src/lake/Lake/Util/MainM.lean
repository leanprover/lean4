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

@[inline] protected def run (self : MainM α) : BaseIO ExitCode :=
  self.toBaseIO.map fun | Except.ok _ => 0 | Except.error rc => rc

/-! # Exits -/

/-- Exit with given return code. -/
@[inline] protected def exit (rc : ExitCode) : MainM α :=
  MainM.mk <| throw rc

instance : MonadExit MainM := ⟨MainM.exit⟩

/-- Try this and catch exits. -/
@[inline] protected def tryCatchExit (f : ExitCode → MainM α) (self : MainM α) : MainM α :=
  self.toEIO.tryCatch f

/-- Try this and catch error codes (i.e., non-zero exits). -/
@[inline] protected def tryCatchError (f : ExitCode → MainM α) (self : MainM α) : MainM α :=
  self.tryCatchExit fun rc => if rc = 0 then exit 0 else f rc

/-- Exit with a generic error code (i.e., 1). -/
@[inline] protected def failure : MainM α :=
  exit 1

/-- If this exits with an error code (i.e., not 0), perform other. -/
@[inline] protected def orElse (self : MainM α) (other : Unit → MainM α) : MainM α :=
  self.tryCatchExit fun rc => if rc = 0 then exit 0 else other ()

instance : Alternative MainM where
  failure := MainM.failure
  orElse := MainM.orElse

/-! # Logging and IO -/

instance : MonadLog MainM := .stderr

/-- Print out a error line with the given message and then exit with an error code. -/
@[inline] protected def error (msg : String) (rc : ExitCode := 1) : MainM α := do
  logError msg
  exit rc

instance : MonadError MainM := ⟨MainM.error⟩
instance : MonadLift IO MainM := ⟨MonadError.runIO⟩

@[inline] def runLogIO (x : LogIO α)
  (minLv := LogLevel.info) (ansiMode := AnsiMode.auto) (out := OutStream.stderr)
: MainM α := do
  match (← x {}) with
  | .ok a  log => replay log (← out.getLogger minLv ansiMode); return a
  | .error _ log => replay log (← out.getLogger .trace ansiMode); exit 1
where
  -- avoid specialization of this call at each call site
  replay (log : Log) (logger : MonadLog BaseIO) : BaseIO Unit :=
    log.replay (logger := logger)

instance (priority := low) : MonadLift LogIO MainM := ⟨runLogIO⟩

@[inline] def runLoggerIO (x : LoggerIO α)
  (minLv := LogLevel.info) (ansiMode := AnsiMode.auto) (out := OutStream.stderr)
: MainM α := do
  let some a ← x.run (← out.getLogger minLv ansiMode) |>.toBaseIO
    | exit 1
  return a

instance (priority := low) : MonadLift LoggerIO MainM := ⟨runLoggerIO⟩
