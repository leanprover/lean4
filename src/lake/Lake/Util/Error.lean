/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.System.IO

namespace Lake

public class MonadError (m : Type u → Type v) where
  error {α : Type u} : String → m α

export MonadError (error)

public instance [MonadLift m n] [MonadError m] : MonadError n where
  error msg := liftM (m := m) <| error msg

public instance : MonadError IO where
  error msg := throw <| IO.userError msg

public instance : MonadError (EIO String) where
  error msg := throw msg

public instance : MonadError (Except String) where
  error msg := throw msg

/--
Perform an EIO action.
If it throws an error, invoke `error` with its string representation.
-/
@[inline] public def MonadError.runEIO
  [Monad m] [MonadError m] [MonadLiftT BaseIO m] [ToString ε] (x : EIO ε α)
: m α := do
  match (← x.toBaseIO) with
  | .ok a => pure a
  | .error e => error (toString e)

/--
Perform an IO action.
If it throws an error, invoke `error` with its string representation.
-/
@[inline] public def MonadError.runIO
  [Monad m] [MonadError m] [MonadLiftT BaseIO m] (x : IO α)
: m α := MonadError.runEIO x
