/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The Reader monad transformer for passing immutable State.
-/

prelude
import Init.Control.MonadControl
import Init.Control.Id
import Init.Control.Alternative
import Init.Control.Except
universes u v w

/-- An implementation of [ReaderT](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Reader.html#t:ReaderT) -/
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
ρ → m α

instance ReaderT.inhabited (ρ : Type u) (m : Type u → Type v) (α : Type u) [Inhabited (m α)] : Inhabited (ReaderT ρ m α) :=
⟨fun _ => arbitrary _⟩

@[inline] def ReaderT.run {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : ReaderT ρ m α) (r : ρ) : m α :=
x r

@[reducible] def Reader (ρ : Type u) := ReaderT ρ id

namespace ReaderT

section
variables {ρ : Type u} {m : Type u → Type v} {α : Type u}

@[inline] protected def lift  (a : m α) : ReaderT ρ m α :=
fun r => a

instance  : MonadLift m (ReaderT ρ m) :=
⟨@ReaderT.lift ρ m⟩

instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (ReaderT ρ m) :=
{ throw := fun α => ReaderT.lift ∘ throwThe ε,
  tryCatch := fun α x c r => tryCatchThe ε (x r) (fun e => (c e) r) }

@[inline] protected def orelse [Alternative m] {α : Type u} (x₁ x₂ : ReaderT ρ m α) : ReaderT ρ m α :=
fun s => x₁ s <|> x₂ s

@[inline] protected def failure [Alternative m] {α : Type u} : ReaderT ρ m α :=
fun s => failure

end

section
variables {ρ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}

@[inline] protected def read : ReaderT ρ m ρ :=
pure

@[inline] protected def pure (a : α) : ReaderT ρ m α :=
fun r => pure a

@[inline] protected def bind (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) : ReaderT ρ m β :=
fun r => do a ← x r; f a r

@[inline] protected def map (f : α → β) (x : ReaderT ρ m α) : ReaderT ρ m β :=
fun r => f <$> x r

instance : Monad (ReaderT ρ m) :=
{ pure := @ReaderT.pure _ _ _, bind := @ReaderT.bind _ _ _, map := @ReaderT.map _ _ _ }

instance (ρ m) [Monad m] : MonadFunctor m (ReaderT ρ m) :=
⟨fun _ f x r => f (x r)⟩

@[inline] protected def adapt {ρ' : Type u} [Monad m] {α : Type u} (f : ρ' → ρ) : ReaderT ρ m α → ReaderT ρ' m α :=
fun x r => x (f r)

instance [Alternative m] : Alternative (ReaderT ρ m) :=
{ ReaderT.Monad with
  failure := @ReaderT.failure _ _ _,
  orelse  := @ReaderT.orelse _ _ _ }

end
end ReaderT

/-- An implementation of [MonadReader](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
    It does not contain `local` because this Function cannot be lifted using `monadLift`.
    Instead, the `MonadReaderAdapter` class provides the more general `adaptReader` Function.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class MonadReader (ρ : outParam (Type u)) (n : Type u → Type u) :=
    (lift {α : Type u} : (∀ {m : Type u → Type u} [Monad m], ReaderT ρ m α) → n α)
    ```
    -/
class MonadReaderOf (ρ : Type u) (m : Type u → Type v) :=
(read : m ρ)

@[inline] def readThe (ρ : Type u) {m : Type u → Type v} [MonadReaderOf ρ m] : m ρ :=
MonadReaderOf.read

/-- Similar to `MonadReaderOf`, but `ρ` is an outParam for convenience -/
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) :=
(read : m ρ)

export MonadReader (read)

instance MonadReaderOf.isMonadReader (ρ : Type u) (m : Type u → Type v) [MonadReaderOf ρ m] : MonadReader ρ m :=
⟨readThe ρ⟩

instance monadReaderTrans {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w}
  [MonadReaderOf ρ m] [MonadLift m n] : MonadReaderOf ρ n :=
⟨monadLift (MonadReader.read : m ρ)⟩

instance {ρ : Type u} {m : Type u → Type v} [Monad m] : MonadReaderOf ρ (ReaderT ρ m) :=
⟨ReaderT.read⟩

instance ReaderT.monadControl (ρ : Type u) (m : Type u → Type v) : MonadControl m (ReaderT ρ m) := {
  stM      := fun α       => α,
  liftWith := fun α f ctx => f fun β x => x ctx,
  restoreM := fun α x ctx => x,
}

instance ReaderT.tryFinally {m : Type u → Type v} {ρ : Type u} [MonadFinally m] [Monad m] : MonadFinally (ReaderT ρ m) :=
{ tryFinally' := fun α β x h ctx => tryFinally' (x ctx) (fun a? => h a? ctx) }

class MonadWithReaderOf (ρ : Type u) (m : Type u → Type v) :=
(withReader {α : Type u} : (ρ → ρ) → m α → m α)

@[inline] def withTheReader (ρ : Type u) {m : Type u → Type v} [MonadWithReaderOf ρ m] {α : Type u} (f : ρ → ρ) (x : m α) : m α :=
MonadWithReaderOf.withReader f x

class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) :=
(withReader {α : Type u} : (ρ → ρ) → m α → m α)

export MonadWithReader (withReader)

instance MonadWithReaderOf.isMonadWithReader (ρ : Type u) (m : Type u → Type v) [MonadWithReaderOf ρ m] : MonadWithReader ρ m :=
⟨fun α => withTheReader ρ⟩

section
variables {ρ : Type u} {m : Type u → Type v}

instance monadWithReaderOfTrans {n : Type u → Type v} [MonadWithReaderOf ρ m] [MonadFunctor m n] : MonadWithReaderOf ρ n :=
⟨fun α f => monadMap fun β => (withTheReader ρ f : m β → m β)⟩

instance ReaderT.monadWithReaderOf [Monad m] : MonadWithReaderOf ρ (ReaderT ρ m) :=
⟨fun α f x ctx => x (f ctx)⟩
end
