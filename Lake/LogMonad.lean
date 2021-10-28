/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.RealM

namespace Lake

-- # Typeclass

class MonadLog (m : Type u → Type v) where
  logInfo : String → m PUnit
  logWarning : String → m PUnit
  logError : String → m PUnit

export MonadLog (logInfo logWarning logError)

instance [MonadLift m n] [MonadLog m] : MonadLog n where
  logInfo msg := liftM (m := m) <| logInfo msg
  logWarning msg := liftM (m := m) <| logWarning msg
  logError msg := liftM (m := m) <| logError msg

-- # Context

structure LogMethods (m : Type → Type) : Type where
  logInfo : String → m PUnit
  logWarning : String → m PUnit
  logError : String → m PUnit

namespace LogMethods

def nop [Pure m] : LogMethods m :=
  ⟨fun _ => pure (), fun _ => pure (), fun _ => pure ()⟩

instance [Pure m] : Inhabited (LogMethods m) := ⟨LogMethods.nop⟩

def io [MonadLiftT RealM m] : LogMethods m where
  logInfo msg := RealM.runIO_ <| IO.println msg
  logWarning msg := RealM.runIO_ <| IO.eprintln s!"warning: {msg}"
  logError msg := RealM.runIO_ <| IO.eprintln s!"error: {msg}"

def eio [MonadLiftT RealM m] : LogMethods m where
  logInfo msg := RealM.runIO_ <| IO.eprintln s!"info: {msg}"
  logWarning msg := RealM.runIO_ <| IO.eprintln s!"warning: {msg}"
  logError msg := RealM.runIO_ <| IO.eprintln s!"error: {msg}"

end LogMethods

-- # Transformer

abbrev LogT (m : Type → Type) :=
  ReaderT (LogMethods m) m

instance [Pure m] [Inhabited α] : Inhabited (LogT m α) :=
  ⟨fun _ => pure Inhabited.default⟩

instance [Monad m] : MonadLog (LogT m) where
  logInfo msg := do (← read).logInfo msg
  logWarning msg := do (← read).logWarning msg
  logError msg := do (← read).logError msg

namespace LogT

abbrev run (methods :  LogMethods m) (self : LogT m α) : m α :=
  ReaderT.run self methods

abbrev runWith (methods :  LogMethods m) (self : LogT m α) : m α :=
  ReaderT.run self methods

abbrev adaptMethods [Monad m] (f : LogMethods m → LogMethods m) (self : LogT m α) : LogT m α :=
  ReaderT.adapt f self

end LogT
