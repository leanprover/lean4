/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Message
import Lean.InternalExceptionId
import Lean.Data.Options

namespace Lean

/- Exception type used in most Lean monads -/
inductive Exception
  | error (ref : Syntax) (msg : MessageData)
  | internal (id : InternalExceptionId)

def Exception.toMessageData : Exception → MessageData
  | Exception.error _ msg => msg
  | Exception.internal id => id.toString

def Exception.getRef : Exception → Syntax
  | Exception.error ref _ => ref
  | Exception.internal _  => Syntax.missing

instance : Inhabited Exception := ⟨Exception.error (arbitrary _) (arbitrary _)⟩

class Ref (m : Type → Type) :=
  (getRef      : m Syntax)
  (withRef {α} : Syntax → m α → m α)

export Ref (getRef)

instance (m n : Type → Type) [Ref m] [MonadFunctor m n] [MonadLift m n] : Ref n := {
  getRef  := liftM (getRef : m _),
  withRef := fun ref x => monadMap (m := m) (Ref.withRef ref) x
}

def replaceRef (ref : Syntax) (oldRef : Syntax) : Syntax :=
  match ref.getPos with
  | some _ => ref
  | _      => oldRef

@[inline] def withRef {m : Type → Type} [Monad m] [Ref m] {α} (ref : Syntax) (x : m α) : m α := do
  let oldRef ← getRef
  let ref := replaceRef ref oldRef
  Ref.withRef ref x

/- Similar to `AddMessageContext`, but for error messages.
   The default instance just uses `AddMessageContext`.
   In error messages, we may want to provide additional information (e.g., macro expansion stack),
   and refine the `(ref : Syntax)`. -/
class AddErrorMessageContext (m : Type → Type) :=
  (add : Syntax → MessageData → m (Syntax × MessageData))

instance (m : Type → Type) [AddMessageContext m] [Monad m] : AddErrorMessageContext m := {
  add := fun ref msg => do
    let msg ← addMessageContext msg
    pure (ref, msg)
}

section Methods

variables {m : Type → Type} [Monad m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m]

def throwError {α} (msg : MessageData) : m α := do
  let ref ← getRef
  let (ref, msg) ← AddErrorMessageContext.add ref msg
  throw $ Exception.error ref msg

def throwUnknownConstant {α} (constName : Name) : m α :=
  throwError msg!"unknown constant '{mkConst constName}'"

def throwErrorAt {α} (ref : Syntax) (msg : MessageData) : m α := do
  withRef ref $ throwError msg

def ofExcept {ε α} [ToString ε] (x : Except ε α) : m α :=
  match x with
  | Except.ok a    => pure a
  | Except.error e => throwError $ toString e

def throwKernelException {α} [MonadOptions m] (ex : KernelException) : m α := do
  throwError $ ex.toMessageData (← getOptions)

end Methods

class MonadRecDepth (m : Type → Type) :=
  (withRecDepth {α} : Nat → m α → m α)
  (getRecDepth      : m Nat)
  (getMaxRecDepth   : m Nat)

instance {ρ m} [Monad m] [MonadRecDepth m] : MonadRecDepth (ReaderT ρ m) := {
  withRecDepth   := fun d x ctx => MonadRecDepth.withRecDepth d (x ctx),
  getRecDepth    := fun _ => MonadRecDepth.getRecDepth,
  getMaxRecDepth := fun _ => MonadRecDepth.getMaxRecDepth
}

instance {ω σ m} [Monad m] [MonadRecDepth m] : MonadRecDepth (StateRefT' ω σ m) :=
  inferInstanceAs (MonadRecDepth (ReaderT _ _))

@[inline] def withIncRecDepth {α m} [Monad m] [MonadRecDepth m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m]
    (x : m α) : m α := do
  let curr ← MonadRecDepth.getRecDepth
  let max  ← MonadRecDepth.getMaxRecDepth
  if curr == max then throwError maxRecDepthErrorMessage
  MonadRecDepth.withRecDepth (curr+1) x

syntax "throwError! " ((interpolatedStr term) <|> term) : term
syntax "throwErrorAt! " term:max ((interpolatedStr term) <|> term) : term

macro_rules
  | `(throwError! $msg) =>
    if msg.getKind == interpolatedStrKind then
      `(throwError (msg! $msg))
    else
      `(throwError $msg)

macro_rules
  | `(throwErrorAt! $ref $msg) =>
    if msg.getKind == interpolatedStrKind then
      `(throwErrorAt $ref (msg! $msg))
    else
      `(throwErrorAt $ref $msg)

end Lean
