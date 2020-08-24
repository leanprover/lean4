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

instance Exception.inhabited : Inhabited Exception := ⟨Exception.error (arbitrary _) (arbitrary _)⟩

class MonadError (m : Type → Type) extends MonadExceptOf Exception m :=
(getRef         : m Syntax)
(addContext     : Syntax → MessageData → m (Syntax × MessageData))
(withRef    {α} : Syntax → m α → m α)

export MonadError (getRef addContext withRef)

instance ReaderT.monadError {ρ m} [Monad m] [MonadError m] : MonadError (ReaderT ρ m) :=
{ getRef        := fun _           => getRef,
  addContext    := fun ref msg _   => addContext ref msg,
  withRef       := fun α ref x ctx => MonadError.withRef ref (x ctx) }

instance StateRefT.monadError {ω σ m} [Monad m] [MonadError m] : MonadError (StateRefT' ω σ m) :=
inferInstanceAs (MonadError (ReaderT _ _))

section Methods

variables {m : Type → Type} [Monad m] [MonadError m]

def throwError {α} (msg : MessageData) : m α := do
ref ← getRef;
(ref, msg) ← addContext ref msg;
throw $ Exception.error ref msg

def replaceRef (ref : Syntax) (oldRef : Syntax) : Syntax :=
match ref.getPos with
| some _ => ref
| _      => oldRef

@[inline] def withRef {α} (ref : Syntax) (x : m α) : m α := do
oldRef ← getRef;
let ref := replaceRef ref oldRef;
MonadError.withRef ref x

def throwErrorAt {α} (ref : Syntax) (msg : MessageData) : m α := do
ctxRef ← getRef;
let ref := replaceRef ref ctxRef;
(ref, msg) ← addContext ref msg;
throw $ Exception.error ref msg

def ofExcept {ε α} [HasToString ε] (x : Except ε α) : m α :=
match x with
| Except.ok a    => pure a
| Except.error e => throwError $ toString e

def throwKernelException {α} [MonadOptions m] (ex : KernelException) : m α := do
opts ← getOptions;
throwError $ ex.toMessageData opts

end Methods

class MonadRecDepth (m : Type → Type) :=
(withRecDepth {α} : Nat → m α → m α)
(getRecDepth      : m Nat)
(getMaxRecDepth   : m Nat)

instance ReaderT.MonadRecDepth {ρ m} [Monad m] [MonadRecDepth m] : MonadRecDepth (ReaderT ρ m) :=
{ withRecDepth := fun α d x ctx => MonadRecDepth.withRecDepth d (x ctx),
  getRecDepth     := fun _ => MonadRecDepth.getRecDepth,
  getMaxRecDepth  := fun _ => MonadRecDepth.getMaxRecDepth }

instance StateRefT.monadRecDepth {ω σ m} [Monad m] [MonadRecDepth m] : MonadRecDepth (StateRefT' ω σ m) :=
inferInstanceAs (MonadRecDepth (ReaderT _ _))

@[inline] def withIncRecDepth {α m} [Monad m] [MonadRecDepth m] [MonadError m] (x : m α) : m α := do
curr ← MonadRecDepth.getRecDepth;
max  ← MonadRecDepth.getMaxRecDepth;
when (curr == max) $ throwError maxRecDepthErrorMessage;
MonadRecDepth.withRecDepth (curr+1) x

end Lean
