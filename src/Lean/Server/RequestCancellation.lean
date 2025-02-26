/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Init.System.Promise

namespace Lean.Server

structure RequestCancellationToken where
  cancelledByCancelRequest : IO.Ref Bool
  cancelledByEdit          : IO.Ref Bool
  cancellationPromise      : IO.Promise Unit

namespace RequestCancellationToken

def new : BaseIO RequestCancellationToken := do
  return {
    cancelledByCancelRequest := ← IO.mkRef false
    cancelledByEdit          := ← IO.mkRef false
    cancellationPromise      := ← IO.Promise.new
  }

def cancelByCancelRequest (tk : RequestCancellationToken) : BaseIO Unit := do
  tk.cancelledByCancelRequest.set true
  tk.cancellationPromise.resolve ()

def cancelByEdit (tk : RequestCancellationToken) : BaseIO Unit := do
  tk.cancelledByEdit.set true
  tk.cancellationPromise.resolve ()

def cancellationTask (tk : RequestCancellationToken) : Task Unit :=
  tk.cancellationPromise.result!

def wasCancelledByCancelRequest (tk : RequestCancellationToken) : BaseIO Bool :=
  tk.cancelledByCancelRequest.get

def wasCancelledByEdit (tk : RequestCancellationToken) : BaseIO Bool := do
  tk.cancelledByEdit.get

end RequestCancellationToken

structure RequestCancellation where

def RequestCancellation.requestCancelled : RequestCancellation := {}

abbrev CancellableT m := ReaderT RequestCancellationToken (ExceptT RequestCancellation m)
abbrev CancellableM := CancellableT IO

def CancellableT.run (tk : RequestCancellationToken) (x : CancellableT m α) :
    m (Except RequestCancellation α) :=
  x tk

def CancellableM.run (tk : RequestCancellationToken) (x : CancellableM α) :
    IO (Except RequestCancellation α) :=
  CancellableT.run tk x

def CancellableT.checkCancelled [Monad m] [MonadLiftT BaseIO m] : CancellableT m Unit := do
  let tk ← read
  if ← tk.wasCancelledByCancelRequest then
    throw .requestCancelled

def CancellableM.checkCancelled : CancellableM Unit :=
  CancellableT.checkCancelled

class MonadCancellable (m : Type → Type v) where
  checkCancelled : m PUnit

instance (m n) [MonadLift m n] [MonadCancellable m] : MonadCancellable n where
  checkCancelled := liftM (MonadCancellable.checkCancelled : m PUnit)

instance [Monad m] [MonadLiftT BaseIO m] : MonadCancellable (CancellableT m) where
  checkCancelled := CancellableT.checkCancelled

def RequestCancellation.check [MonadCancellable m] : m Unit :=
  MonadCancellable.checkCancelled
