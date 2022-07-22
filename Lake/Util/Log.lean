/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Error

namespace Lake

inductive LogLevel
| info
| warning
| error

/-! # Class -/

class MonadLog (m : Type u → Type v) where
  log (message : String) (level : LogLevel) : m PUnit

export MonadLog (log)

abbrev logInfo [MonadLog m] (message : String) : m PUnit :=
  log message .info

abbrev logWarning [MonadLog m] (message : String) : m PUnit :=
  log message .warning

abbrev logError  [MonadLog m] (message : String) : m PUnit :=
  log message .error

namespace MonadLog

def nop [Pure m] : MonadLog m :=
  ⟨fun _ _ => pure ()⟩

instance [Pure m] : Inhabited (MonadLog m) := ⟨MonadLog.nop⟩

def io [MonadLiftT BaseIO m] : MonadLog m where
  log msg
    | .info => IO.println msg.trim |>.catchExceptions fun _ => pure ()
    | .warning => IO.eprintln s!"warning: {msg.trim}" |>.catchExceptions fun _ => pure ()
    | .error => IO.eprintln s!"error: {msg.trim}" |>.catchExceptions fun _ => pure ()

def eio [MonadLiftT BaseIO m] : MonadLog m where
  log msg
    | .info => IO.eprintln s!"info: {msg.trim}"  |>.catchExceptions fun _ => pure ()
    | .warning => IO.eprintln s!"warning: {msg.trim}" |>.catchExceptions fun _ => pure ()
    | .error => IO.eprintln s!"error: {msg.trim}" |>.catchExceptions fun _ => pure ()

def lift [MonadLiftT m n] (self : MonadLog m) : MonadLog n where
  log msg lv := liftM <| self.log msg lv

instance [MonadLift m n] [methods : MonadLog m] : MonadLog n  := lift methods

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
  log msg lv := do (← read).log msg lv

namespace MonadLogT

abbrev run (methods : MonadLog m) (self : MonadLogT m n α) : n α :=
  ReaderT.run self methods

abbrev runWith (methods : MonadLog m) (self : MonadLogT m n α) : n α :=
  ReaderT.run self methods

abbrev adaptMethods [Monad n]
(f : MonadLog m → MonadLog m') (self : MonadLogT m' n α) : MonadLogT m n α :=
  ReaderT.adapt f self

end MonadLogT

abbrev LogIO :=
  MonadLogT BaseIO IO

abbrev LogT (m : Type → Type) :=
  MonadLogT m m

namespace LogT

def run (methods : MonadLog m) (self : LogT m α) : m α :=
  ReaderT.run self methods

def runWith (methods : MonadLog m) (self : LogT m α) : m α :=
  ReaderT.run self methods

end LogT
