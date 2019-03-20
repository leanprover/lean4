/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The reader monad transformer for passing immutable state.
-/

prelude
import init.control.lift init.control.id init.control.alternative init.control.except
universes u v w

/-- An implementation of [ReaderT](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Reader.html#t:ReaderT) -/
def readerT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
ρ → m α

@[inline] def readerT.run {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : readerT ρ m α) (r : ρ) : m α :=
x r

@[reducible] def reader (ρ : Type u) := readerT ρ id

namespace readerT
section
  variable  {ρ : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}

  @[inline] protected def read : readerT ρ m ρ :=
  pure

  @[inline] protected def pure (a : α) : readerT ρ m α :=
  λ r, pure a

  @[inline] protected def bind (x : readerT ρ m α) (f : α → readerT ρ m β) : readerT ρ m β :=
  λ r, do a ← x r,
          f a r

  instance : monad (readerT ρ m) :=
  { pure := @readerT.pure _ _ _, bind := @readerT.bind _ _ _ }

  @[inline] protected def lift (a : m α) : readerT ρ m α :=
  λ r, a

  instance (m) [monad m] : hasMonadLift m (readerT ρ m) :=
  ⟨@readerT.lift ρ m _⟩

  instance (ρ m m') [monad m] [monad m'] : monadFunctor m m' (readerT ρ m) (readerT ρ m') :=
  ⟨λ _ f x, λ r, f (x r)⟩

  @[inline] protected def adapt {ρ' : Type u} [monad m] {α : Type u} (f : ρ' → ρ) : readerT ρ m α → readerT ρ' m α :=
  λ x r, x (f r)

  @[inline] protected def orelse [alternative m] {α : Type u} (x₁ x₂ : readerT ρ m α) : readerT ρ m α :=
  λ s, x₁ s <|> x₂ s

  @[inline] protected def failure [alternative m] {α : Type u} : readerT ρ m α :=
  λ s, failure

  instance [alternative m] : alternative (readerT ρ m) :=
  { failure := @readerT.failure _ _ _ _,
    orelse  := @readerT.orelse _ _ _ _,
    ..readerT.monad }

  instance (ε) [monad m] [monadExcept ε m] : monadExcept ε (readerT ρ m) :=
  { throw := λ α, readerT.lift ∘ throw,
    catch := λ α x c r, catch (x r) (λ e, (c e) r) }
end
end readerT


/-- An implementation of [MonadReader](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
    It does not contain `local` because this function cannot be lifted using `monadLift`.
    Instead, the `monadReaderAdapter` class provides the more general `adaptReader` function.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monadReader (ρ : outParam (Type u)) (n : Type u → Type u) :=
    (lift {} {α : Type u} : (∀ {m : Type u → Type u} [monad m], readerT ρ m α) → n α)
    ```
    -/
class monadReader (ρ : outParam (Type u)) (m : Type u → Type v) :=
(read {} : m ρ)

export monadReader (read)

instance monadReaderTrans {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w}
  [hasMonadLift m n] [monadReader ρ m] : monadReader ρ n :=
⟨monadLift (monadReader.read : m ρ)⟩

instance {ρ : Type u} {m : Type u → Type v} [monad m] : monadReader ρ (readerT ρ m) :=
⟨readerT.read⟩


/-- Adapt a monad stack, changing the type of its top-most environment.

    This class is comparable to [Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify), but does not use lenses (why would it), and is derived automatically for any transformer implementing `monadFunctor`.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monadReaderFunctor (ρ ρ' : outParam (Type u)) (n n' : Type u → Type u) :=
    (map {} {α : Type u} : (∀ {m : Type u → Type u} [monad m], readerT ρ m α → readerT ρ' m α) → n α → n' α)
    ```
    -/
class monadReaderAdapter (ρ ρ' : outParam (Type u)) (m m' : Type u → Type v) :=
(adaptReader {} {α : Type u} : (ρ' → ρ) → m α → m' α)
export monadReaderAdapter (adaptReader)

section
variables {ρ ρ' : Type u} {m m' : Type u → Type v}

instance monadReaderAdapterTrans {n n' : Type u → Type v} [monadFunctor m m' n n'] [monadReaderAdapter ρ ρ' m m'] : monadReaderAdapter ρ ρ' n n' :=
⟨λ α f, monadMap (λ α, (adaptReader f : m α → m' α))⟩

instance [monad m] : monadReaderAdapter ρ ρ' (readerT ρ m) (readerT ρ' m) :=
⟨λ α, readerT.adapt⟩
end

instance (ρ : Type u) (m out) [monadRun out m] : monadRun (λ α, ρ → out α) (readerT ρ m) :=
⟨λ α x, run ∘ x⟩

class monadReaderRunner (ρ : Type u) (m m' : Type u → Type u) :=
(runReader {} {α : Type u} : m α → ρ → m' α)
export monadReaderRunner (runReader)

section
variables {ρ ρ' : Type u} {m m' : Type u → Type u}

instance monadReaderRunnerTrans {n n' : Type u → Type u} [monadFunctor m m' n n'] [monadReaderRunner ρ m m'] : monadReaderRunner ρ n n' :=
⟨λ α x r, monadMap (λ α (y : m α), (runReader y r : m' α)) x⟩

instance readerT.monadStateRunner [monad m] : monadReaderRunner ρ (readerT ρ m) m :=
⟨λ α x r, x r⟩
end
