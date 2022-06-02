/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Error

namespace Lake

-- # Class

class MonadLog (m : Type u → Type v) where
  logInfo : String → m PUnit
  logWarning : String → m PUnit
  logError : String → m PUnit

export MonadLog (logInfo logWarning logError)

namespace MonadLog

def nop [Pure m] : MonadLog m :=
  ⟨fun _ => pure (), fun _ => pure (), fun _ => pure ()⟩

instance [Pure m] : Inhabited (MonadLog m) := ⟨MonadLog.nop⟩

def io [MonadLiftT BaseIO m] : MonadLog m where
  logInfo msg := IO.println msg |>.catchExceptions fun _ => pure ()
  logWarning msg := IO.eprintln s!"warning: {msg}" |>.catchExceptions fun _ => pure ()
  logError msg := IO.eprintln s!"error: {msg}" |>.catchExceptions fun _ => pure ()

def eio [MonadLiftT BaseIO m] : MonadLog m where
  logInfo msg := IO.eprintln s!"info: {msg}" |>.catchExceptions fun _ => pure ()
  logWarning msg := IO.eprintln s!"warning: {msg}" |>.catchExceptions fun _ => pure ()
  logError msg := IO.eprintln s!"error: {msg}" |>.catchExceptions fun _ => pure ()

def lift [MonadLiftT m n] (self : MonadLog m) : MonadLog n where
  logInfo msg := liftM <| self.logInfo msg
  logWarning msg := liftM <| self.logWarning msg
  logError msg := liftM <| self.logError msg

instance [MonadLift m n] [methods : MonadLog m] : MonadLog n  := lift methods

/-- Log the given error message and then fail. -/
protected def error [Alternative m] [MonadLog m] (msg : String) : m α :=
  logError msg *> failure

end MonadLog

-- # Transformers

abbrev MonadLogT (m : Type u → Type v) (n : Type v → Type w) :=
   ReaderT (MonadLog m) n

instance [Pure n] [Inhabited α] : Inhabited (MonadLogT m n α) :=
  ⟨fun _ => pure Inhabited.default⟩

instance [Monad n] [MonadLiftT m n] : MonadLog (MonadLogT m n) where
  logInfo msg := do (← read).logInfo msg
  logWarning msg := do (← read).logWarning msg
  logError msg := do (← read).logError msg

namespace MonadLogT

abbrev run (methods : MonadLog m) (self : MonadLogT m n α) : n α :=
  ReaderT.run self methods

abbrev runWith (methods : MonadLog m) (self : MonadLogT m n α) : n α :=
  ReaderT.run self methods

abbrev adaptMethods [Monad n]
(f : MonadLog m → MonadLog m') (self : MonadLogT m' n α) : MonadLogT m n α :=
  ReaderT.adapt f self

end MonadLogT

abbrev LogT (m : Type → Type) :=
  MonadLogT m m

namespace LogT

def run (methods : MonadLog m) (self : LogT m α) : m α :=
  ReaderT.run self methods

def runWith (methods : MonadLog m) (self : LogT m α) : m α :=
  ReaderT.run self methods

end LogT
