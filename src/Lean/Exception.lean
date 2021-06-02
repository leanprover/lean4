/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Message
import Lean.InternalExceptionId
import Lean.Data.Options
import Lean.Util.MonadCache

namespace Lean

/- Exception type used in most Lean monads -/
inductive Exception where
  | error (ref : Syntax) (msg : MessageData)
  | internal (id : InternalExceptionId) (extra : KVMap := {})

def Exception.toMessageData : Exception → MessageData
  | Exception.error _ msg   => msg
  | Exception.internal id _ => id.toString

def Exception.getRef : Exception → Syntax
  | Exception.error ref _   => ref
  | Exception.internal _  _ => Syntax.missing

instance : Inhabited Exception := ⟨Exception.error arbitrary arbitrary⟩

/- Similar to `AddMessageContext`, but for error messages.
   The default instance just uses `AddMessageContext`.
   In error messages, we may want to provide additional information (e.g., macro expansion stack),
   and refine the `(ref : Syntax)`. -/
class AddErrorMessageContext (m : Type → Type) where
  add : Syntax → MessageData → m (Syntax × MessageData)

instance (m : Type → Type) [AddMessageContext m] [Monad m] : AddErrorMessageContext m where
  add ref msg := do
    let msg ← addMessageContext msg
    pure (ref, msg)

class abbrev MonadError (m : Type → Type) :=
  MonadExceptOf Exception m
  MonadRef m
  AddErrorMessageContext m

section Methods

protected def throwError [Monad m] [MonadError m] (msg : MessageData) : m α := do
  let ref ← getRef
  let (ref, msg) ← AddErrorMessageContext.add ref msg
  throw <| Exception.error ref msg

def throwUnknownConstant [Monad m] [MonadError m] (constName : Name) : m α :=
  Lean.throwError m!"unknown constant '{mkConst constName}'"

protected def throwErrorAt [Monad m] [MonadError m] (ref : Syntax) (msg : MessageData) : m α := do
  withRef ref <| Lean.throwError msg

def ofExcept [Monad m] [MonadError m] [ToString ε] (x : Except ε α) : m α :=
  match x with
  | Except.ok a    => pure a
  | Except.error e => Lean.throwError $ toString e

def throwKernelException [Monad m] [MonadError m] [MonadOptions m] (ex : KernelException) : m α := do
  Lean.throwError <| ex.toMessageData (← getOptions)

end Methods

class MonadRecDepth (m : Type → Type) where
  withRecDepth {α} : Nat → m α → m α
  getRecDepth      : m Nat
  getMaxRecDepth   : m Nat

instance [Monad m] [MonadRecDepth m] : MonadRecDepth (ReaderT ρ m) where
  withRecDepth d x := fun ctx => MonadRecDepth.withRecDepth d (x ctx)
  getRecDepth      := fun _ => MonadRecDepth.getRecDepth
  getMaxRecDepth   := fun _ => MonadRecDepth.getMaxRecDepth

instance [Monad m] [MonadRecDepth m] : MonadRecDepth (StateRefT' ω σ m) :=
  inferInstanceAs (MonadRecDepth (ReaderT _ _))

instance [BEq α] [Hashable α] [Monad m] [STWorld ω m] [MonadRecDepth m] : MonadRecDepth (MonadCacheT α β m) :=
  inferInstanceAs (MonadRecDepth (StateRefT' _ _ _))

@[inline] def withIncRecDepth [Monad m] [MonadError m] [MonadRecDepth m] (x : m α) : m α := do
  let curr ← MonadRecDepth.getRecDepth
  let max  ← MonadRecDepth.getMaxRecDepth
  if curr == max then Lean.throwError maxRecDepthErrorMessage
  MonadRecDepth.withRecDepth (curr+1) x

syntax "throwError " (interpolatedStr(term) <|> term) : term
syntax "throwErrorAt " term:max (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwError $msg) =>
    if msg.getKind == interpolatedStrKind then
      `(Lean.throwError (m! $msg))
    else
      `(Lean.throwError $msg)

macro_rules
  | `(throwErrorAt $ref $msg) =>
    if msg.getKind == interpolatedStrKind then
      `(Lean.throwErrorAt $ref (m! $msg))
    else
      `(Lean.throwErrorAt $ref $msg)

end Lean
