/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
namespace Lake

/-- An `IO`/`EIO` monad that can't error. -/
def RealM := EIO Empty

instance : Monad RealM := inferInstanceAs (Monad (EIO Empty))
instance  [Inhabited α] : Inhabited (RealM α) := inferInstanceAs (Inhabited (EIO Empty α))

namespace RealM

abbrev run (self : RealM α) : EIO Empty α :=
  self

def toEIO (self : RealM α) : EIO ε α :=
  fun s => match self s with
  | EStateM.Result.ok a s => EStateM.Result.ok a s

instance : MonadLift RealM (EIO ε) := ⟨toEIO⟩

abbrev toIO (self : RealM α) : IO α :=
  self.toEIO

def runEIO (f : ε → RealM α) (x : EIO ε α) : RealM α :=
  x.catchExceptions f

abbrev runIO (f : IO.Error → RealM α) (x : IO α) : RealM α :=
  runEIO f x

def runEIO' (x : EIO ε α) : RealM (Except ε α) :=
  fun s => match x s with
  | EStateM.Result.ok a s => EStateM.Result.ok (Except.ok a) s
  | EStateM.Result.error e s => EStateM.Result.ok (Except.error e) s

abbrev runIO' (x : IO α) : RealM (Except IO.Error α) :=
  runEIO' x

def runEIO_ (x : EIO ε α) : RealM PUnit :=
  fun s => match x s with
  | EStateM.Result.ok a s => EStateM.Result.ok () s
  | EStateM.Result.error e s => EStateM.Result.ok () s

abbrev runIO_ (x : IO α) : RealM PUnit :=
  runEIO_ x
