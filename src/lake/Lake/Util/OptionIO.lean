/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
namespace Lake

/-- Conceptually identical to `OptionT BaseIO`, but practically more efficient. -/
def OptionIO := EIO PUnit

instance : Monad OptionIO := inferInstanceAs (Monad (EIO PUnit))
instance : MonadLift BaseIO OptionIO := inferInstanceAs (MonadLift BaseIO (EIO PUnit))

namespace OptionIO

@[inline] def mk (x : EIO PUnit α) : OptionIO α :=
  x

@[inline] def toBaseIO (self : OptionIO α) : BaseIO (Option α) :=
  fun s => match self s with
  | EStateM.Result.ok a s => EStateM.Result.ok (some a) s
  | EStateM.Result.error _ s => EStateM.Result.ok none s

@[inline] def toEIO (self : OptionIO α) : EIO PUnit α :=
  self

@[inline] def toIO (f : Unit → IO.Error) (self : OptionIO α) : IO α :=
  self.toEIO.toIO f

@[inline] def catchFailure (f : Unit → BaseIO α) (self : OptionIO α) : BaseIO α :=
  self.toEIO.catchExceptions f

@[inline] protected def failure : OptionIO α :=
  mk <| throw ()

@[inline] protected def orElse (self : OptionIO α) (f : Unit → OptionIO α) : OptionIO α :=
  mk <| tryCatch self.toEIO f

instance : Alternative OptionIO where
  failure := OptionIO.failure
  orElse := OptionIO.orElse

@[always_inline] instance OptionIO.finally : MonadFinally OptionIO where
  tryFinally' := fun x h => do
    match (← x.toBaseIO) with
    | some a => h (some a) <&> ((a, ·))
    | none => h none *> failure

def asTask (self : OptionIO α) (prio := Task.Priority.dedicated) : BaseIO (Task (Option α)) :=
  self.toBaseIO.asTask prio
