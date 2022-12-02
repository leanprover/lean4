/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Error
import Lake.Util.OptionIO

namespace Lake

inductive LogLevel
| info
| warning
| error

inductive Verbosity : Type u
| quiet
| normal
| verbose
deriving BEq

instance : Inhabited Verbosity := ⟨.normal⟩

/-! # Class -/

class MonadLog (m : Type u → Type v) where
  getVerbosity : m Verbosity
  log (message : String) (level : LogLevel) : m PUnit

export MonadLog (log getVerbosity)

def getIsVerbose [Functor m] [MonadLog m] : m Bool :=
  getVerbosity <&> (· == .verbose)

def getIsQuiet [Functor m] [MonadLog m] : m Bool :=
  getVerbosity <&> (· == .quiet)

@[inline] def logVerbose [Monad m] [MonadLog m] (message : String) : m PUnit := do
  if (← getIsVerbose) then log message .info

@[inline] def logInfo [Monad m] [MonadLog m] (message : String) : m PUnit := do
  if !(← getIsQuiet) then log message .info

abbrev logWarning [MonadLog m] (message : String) : m PUnit :=
  log message .warning

abbrev logError  [MonadLog m] (message : String) : m PUnit :=
  log message .error

namespace MonadLog

def nop [Pure m] : MonadLog m :=
  ⟨pure .normal, fun _ _ => pure ()⟩

instance [Pure m] : Inhabited (MonadLog m) := ⟨MonadLog.nop⟩

def io [MonadLiftT BaseIO m] (verbosity := Verbosity.normal) : MonadLog m where
  getVerbosity := (pure verbosity : BaseIO _)
  log msg
    | .info => IO.println msg.trim |>.catchExceptions fun _ => pure ()
    | .warning => IO.eprintln s!"warning: {msg.trim}" |>.catchExceptions fun _ => pure ()
    | .error => IO.eprintln s!"error: {msg.trim}" |>.catchExceptions fun _ => pure ()

def eio [MonadLiftT BaseIO m] (verbosity := Verbosity.normal) : MonadLog m where
  getVerbosity := (pure verbosity : BaseIO _)
  log msg
    | .info => IO.eprintln s!"info: {msg.trim}" |>.catchExceptions fun _ => pure ()
    | .warning => IO.eprintln s!"warning: {msg.trim}" |>.catchExceptions fun _ => pure ()
    | .error => IO.eprintln s!"error: {msg.trim}" |>.catchExceptions fun _ => pure ()

def lift [MonadLiftT m n] (self : MonadLog m) : MonadLog n where
  getVerbosity := liftM <| self.getVerbosity
  log msg lv := liftM <| self.log msg lv

instance [MonadLift m n] [methods : MonadLog m] : MonadLog n := lift methods

/-- Log the given error message and then fail. -/
protected def error [Alternative m] [MonadLog m] (msg : String) : m α :=
  logError msg *> failure

end MonadLog

/-! # Transformers -/

abbrev MonadLogT (m : Type u → Type v) (n : Type v → Type w) :=
   ReaderT (MonadLog m) n

instance [Pure n] [Inhabited α] : Inhabited (MonadLogT m n α) :=
  ⟨fun _ => pure Inhabited.default⟩

instance [Monad n] [MonadLiftT m n] : MonadLog (MonadLogT m n) where
  getVerbosity := do (← read).getVerbosity
  log msg lv := do (← read).log msg lv

abbrev MonadLogT.adaptMethods [Monad n]
(f : MonadLog m → MonadLog m') (self : MonadLogT m' n α) : MonadLogT m n α :=
  ReaderT.adapt f self

abbrev MonadLogT.ignoreLog [Pure m] (self : MonadLogT m n α) : n α :=
  self MonadLog.nop

abbrev LogIO :=
  MonadLogT BaseIO OptionIO

instance : MonadError LogIO := ⟨MonadLog.error⟩
instance : MonadLift IO LogIO := ⟨MonadError.runIO⟩

def LogIO.captureLog (self : LogIO α) (verbosity := Verbosity.normal) : BaseIO (String × Option α) :=
  IO.FS.withIsolatedStreams <| self (MonadLog.eio verbosity) |>.toBaseIO

abbrev LogT (m : Type → Type) :=
  MonadLogT m m
