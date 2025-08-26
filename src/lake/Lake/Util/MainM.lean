/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Log
public import Lake.Util.Exit
public import Lake.Util.Error

namespace Lake

/--
The monad in Lake for `main`-like functions.
Supports IO, logging, and `exit`.
-/
@[expose] public def MainM := EIO ExitCode

public instance : Monad MainM := inferInstanceAs (Monad (EIO ExitCode))
public instance : MonadFinally MainM := inferInstanceAs (MonadFinally (EIO ExitCode))
public instance : MonadLift BaseIO MainM := inferInstanceAs (MonadLift BaseIO (EIO ExitCode))

namespace MainM

/-! # Basics -/

@[inline] public def mk (x : EIO ExitCode α) : MainM α :=
  x

@[inline] public def toEIO (self : MainM α) : EIO ExitCode α :=
  self

@[inline] public def toBaseIO (self : MainM α) : BaseIO (Except ExitCode α) :=
  self.toEIO.toBaseIO

@[inline] public def run (self : MainM α) : BaseIO ExitCode :=
  self.toBaseIO.map fun | Except.ok _ => 0 | Except.error rc => rc

/-! # Exits -/

/-- Exit with given return code. -/
@[inline] public protected def exit (rc : ExitCode) : MainM α :=
  MainM.mk <| throw rc

public instance : MonadExit MainM := ⟨MainM.exit⟩

/-- Try this and catch exits. -/
@[inline] public def tryCatchExit (f : ExitCode → MainM α) (self : MainM α) : MainM α :=
  self.toEIO.tryCatch f

/-- Try this and catch error codes (i.e., non-zero exits). -/
@[inline] public def tryCatchError (f : ExitCode → MainM α) (self : MainM α) : MainM α :=
  self.tryCatchExit fun rc => if rc = 0 then exit 0 else f rc

/-- Exit with a generic error code (i.e., 1). -/
@[inline] public protected def failure : MainM α :=
  exit 1

/-- If this exits with an error code (i.e., not 0), perform other. -/
@[inline] public protected def orElse (self : MainM α) (other : Unit → MainM α) : MainM α :=
  self.tryCatchExit fun rc => if rc = 0 then exit 0 else other ()

instance : Alternative MainM where
  failure := MainM.failure
  orElse := MainM.orElse

/-! # Logging and IO -/

public instance : MonadLog MainM := .stderr

/-- Print out a error line with the given message and then exit with an error code. -/
@[inline] public protected def error (msg : String) (rc : ExitCode := 1) : MainM α := do
  logError msg
  exit rc

public instance : MonadError MainM := ⟨MainM.error⟩
public instance : MonadLift IO MainM := ⟨MonadError.runIO⟩

@[inline] public def runLogIO (x : LogIO α)
  (minLv := LogLevel.info) (ansiMode := AnsiMode.auto) (out := OutStream.stderr)
: MainM α := do
  match (← x.run {}) with
  | .ok a  log => replay log (← out.getLogger minLv ansiMode); return a
  | .error _ log => replay log (← out.getLogger .trace ansiMode); exit 1
where
  -- avoid specialization of this call at each call site
  replay (log : Log) (logger : MonadLog BaseIO) : BaseIO Unit :=
    log.replay (logger := logger)

public instance (priority := low) : MonadLift LogIO MainM := ⟨runLogIO⟩

@[inline] public def runLoggerIO (x : LoggerIO α)
  (minLv := LogLevel.info) (ansiMode := AnsiMode.auto) (out := OutStream.stderr)
: MainM α := do
  let some a ← x.run (← out.getLogger minLv ansiMode) |>.toBaseIO
    | exit 1
  return a

public instance (priority := low) : MonadLift LoggerIO MainM := ⟨runLoggerIO⟩
