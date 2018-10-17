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
def reader_t (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
ρ → m α

@[inline] def reader_t.run {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : reader_t ρ m α) (r : ρ) : m α :=
x r

@[reducible] def reader (ρ : Type u) := reader_t ρ id

namespace reader_t
section
  variable  {ρ : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}

  @[inline] protected def read : reader_t ρ m ρ :=
  pure

  @[inline] protected def pure (a : α) : reader_t ρ m α :=
  λ r, pure a

  @[inline] protected def bind (x : reader_t ρ m α) (f : α → reader_t ρ m β) : reader_t ρ m β :=
  λ r, do a ← x r,
          f a r

  instance : monad (reader_t ρ m) :=
  { pure := @reader_t.pure _ _ _, bind := @reader_t.bind _ _ _ }

  @[inline] protected def lift (a : m α) : reader_t ρ m α :=
  λ r, a

  instance (m) [monad m] : has_monad_lift m (reader_t ρ m) :=
  ⟨@reader_t.lift ρ m _⟩

  instance (ρ m m') [monad m] [monad m'] : monad_functor m m' (reader_t ρ m) (reader_t ρ m') :=
  ⟨λ _ f x, λ r, f (x r)⟩

  @[inline] protected def adapt {ρ' : Type u} [monad m] {α : Type u} (f : ρ' → ρ) : reader_t ρ m α → reader_t ρ' m α :=
  λ x r, x (f r)

  @[inline] protected def orelse [alternative m] {α : Type u} (x₁ x₂ : reader_t ρ m α) : reader_t ρ m α :=
  λ s, x₁ s <|> x₂ s

  @[inline] protected def failure [alternative m] {α : Type u} : reader_t ρ m α :=
  λ s, failure

  instance [alternative m] : alternative (reader_t ρ m) :=
  { failure := @reader_t.failure _ _ _ _,
    orelse  := @reader_t.orelse _ _ _ _,
    ..reader_t.monad }

  instance (ε) [monad m] [monad_except ε m] : monad_except ε (reader_t ρ m) :=
  { throw := λ α, reader_t.lift ∘ throw,
    catch := λ α x c r, catch (x r) (λ e, (c e) r) }
end
end reader_t


/-- An implementation of [MonadReader](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
    It does not contain `local` because this function cannot be lifted using `monad_lift`.
    Instead, the `monad_reader_adapter` class provides the more general `adapt_reader` function.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_reader (ρ : out_param (Type u)) (n : Type u → Type u) :=
    (lift {} {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α) → n α)
    ```
    -/
class monad_reader (ρ : out_param (Type u)) (m : Type u → Type v) :=
(read {} : m ρ)

export monad_reader (read)

instance monad_reader_trans {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w}
  [has_monad_lift m n] [monad_reader ρ m] : monad_reader ρ n :=
⟨monad_lift (monad_reader.read : m ρ)⟩

instance {ρ : Type u} {m : Type u → Type v} [monad m] : monad_reader ρ (reader_t ρ m) :=
⟨reader_t.read⟩


/-- Adapt a monad stack, changing the type of its top-most environment.

    This class is comparable to [Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify), but does not use lenses (why would it), and is derived automatically for any transformer implementing `monad_functor`.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_reader_functor (ρ ρ' : out_param (Type u)) (n n' : Type u → Type u) :=
    (map {} {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α → reader_t ρ' m α) → n α → n' α)
    ```
    -/
class monad_reader_adapter (ρ ρ' : out_param (Type u)) (m m' : Type u → Type v) :=
(adapt_reader {} {α : Type u} : (ρ' → ρ) → m α → m' α)
export monad_reader_adapter (adapt_reader)

section
variables {ρ ρ' : Type u} {m m' : Type u → Type v}

instance monad_reader_adapter_trans {n n' : Type u → Type v} [monad_functor m m' n n'] [monad_reader_adapter ρ ρ' m m'] : monad_reader_adapter ρ ρ' n n' :=
⟨λ α f, monad_map (λ α, (adapt_reader f : m α → m' α))⟩

instance [monad m] : monad_reader_adapter ρ ρ' (reader_t ρ m) (reader_t ρ' m) :=
⟨λ α, reader_t.adapt⟩
end

instance (ρ : Type u) (m out) [monad_run out m] : monad_run (λ α, ρ → out α) (reader_t ρ m) :=
⟨λ α x, run ∘ x⟩

class monad_reader_runner (ρ : Type u) (m m' : Type u → Type u) :=
(run_reader {} {α : Type u} : m α → ρ → m' α)
export monad_reader_runner (run_reader)

section
variables {ρ ρ' : Type u} {m m' : Type u → Type u}

instance monad_reader_runner_trans {n n' : Type u → Type u} [monad_functor m m' n n'] [monad_reader_runner ρ m m'] : monad_reader_runner ρ n n' :=
⟨λ α x r, monad_map (λ α (y : m α), (run_reader y r : m' α)) x⟩

instance reader_t.monad_state_runner [monad m] : monad_reader_runner ρ (reader_t ρ m) m :=
⟨λ α x r, x r⟩
end
