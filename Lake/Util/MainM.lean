/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
namespace Lake

/-- A process exit / return code. -/
abbrev ExitCode := UInt32

class MonadExit (m : Type u → Type v) where
  exit {α : Type u} : ExitCode → m α

export MonadExit (exit)

instance [MonadLift m n] [MonadExit m] : MonadExit n where
  exit rc := liftM (m := m) <| exit rc

abbrev MainM := EIO ExitCode

namespace MainM

@[inline] protected def mk (x : EIO ExitCode α) : MainM α :=
  x

@[inline] protected def toEIO (self : MainM α) : EIO ExitCode α :=
  self

@[inline] protected def toBaseIO (self : MainM α) : BaseIO (Except ExitCode α) :=
  self.toEIO.toBaseIO

protected def run (self : MainM PUnit) : BaseIO ExitCode :=
  self.toBaseIO.map fun | Except.ok _ => 0 | Except.error rc => rc

/-- Exit with given return code. -/
protected def exit (rc : ExitCode) : MainM α :=
  MainM.mk <| throw rc

instance : MonadExit MainM := ⟨MainM.exit⟩

/-- Try this and catch exits. -/
protected def catchExit (f : ExitCode → MainM α) (self : MainM α) : MainM α :=
  self.toEIO.tryCatch f

/-- Exit with a generic error code (i.e., 1). -/
protected def failure : MainM α :=
  exit 1

/-- If this exits with a error code, perform other. -/
protected def orElse (self : MainM α) (other : Unit → MainM α) : MainM α :=
  self.catchExit fun rc => if rc = 0 then exit 0 else other ()

instance : Alternative MainM where
  failure := MainM.failure
  orElse := MainM.orElse

/-- Perform an IO action and silently exit with the given code (default: 1) if it errors. -/
protected def runIO (x : IO α) (rc : ExitCode := 1) : MainM α :=
  x.toEIO fun e => rc
