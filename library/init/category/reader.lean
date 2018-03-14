/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The reader monad transformer for passing immutable state.
-/

prelude
import init.category.lift init.category.id init.category.alternative
universes u v w

/-- An implementation of [ReaderT](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Reader.html#t:ReaderT) -/
structure reader_t (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
(run : ρ → m α)

@[reducible] def reader (ρ : Type u) := reader_t ρ id

attribute [pp_using_anonymous_constructor] reader_t

namespace reader_t
section
  variable  {ρ : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}

  protected def read : reader_t ρ m ρ :=
  ⟨pure⟩

  protected def pure (a : α) : reader_t ρ m α :=
  ⟨λ r, pure a⟩

  protected def bind (x : reader_t ρ m α) (f : α → reader_t ρ m β) : reader_t ρ m β :=
  ⟨λ r, do a ← x.run r,
           (f a).run r⟩

  instance : monad (reader_t ρ m) :=
  { pure := @reader_t.pure _ _ _, bind := @reader_t.bind _ _ _ }

  protected def lift (a : m α) : reader_t ρ m α :=
  ⟨λ r, a⟩

  instance (m) [monad m] : has_monad_lift m (reader_t ρ m) :=
  ⟨@reader_t.lift ρ m _⟩

  protected def monad_map {r m m'} [monad m] [monad m'] {α} (f : Π {α}, m α → m' α) : reader_t r m α → reader_t r m' α :=
  λ x, ⟨λ r, f (x.run r)⟩

  instance (r m m') [monad m] [monad m'] : monad_functor m m' (reader_t r m) (reader_t r m') :=
  ⟨@reader_t.monad_map r m m' _ _⟩

  protected def orelse [alternative m] {α : Type u} (x₁ x₂ : reader_t ρ m α) : reader_t ρ m α :=
  ⟨λ s, x₁.run s <|> x₂.run s⟩

  protected def failure [alternative m] {α : Type u} : reader_t ρ m α :=
  ⟨λ s, failure⟩

  instance [alternative m] : alternative (reader_t ρ m) :=
  { failure := @reader_t.failure _ _ _ _,
    orelse  := @reader_t.orelse _ _ _ _ }
end
end reader_t


/-- An implementation of [MonadReader](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
    It does not contain `local` because this function cannot be lifted using `monad_lift`.
    Instead, the `monad_reader_functor` class provides the more general `with_reader` function. -/
class monad_reader (ρ : out_param (Type u)) (m : Type u → Type v) :=
(lift {} {α : Type u} : reader ρ α → m α)

instance monad_reader_trans {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w}
  [has_monad_lift m n] [monad_reader ρ m] : monad_reader ρ n :=
⟨λ α x, monad_lift (monad_reader.lift x : m α)⟩

instance {ρ : Type u} {m : Type u → Type v} [monad m] : monad_reader ρ (reader_t ρ m) :=
⟨λ α x, ⟨λ r, pure $ x.run r⟩⟩

/-- Read the value of the top-most environment in a monad stack. -/
def monad_reader.read {ρ : Type u} {m : Type u → Type v} [monad_reader ρ m] : m ρ :=
monad_reader.lift (reader_t.read : reader ρ _)
export monad_reader (read)


/-- A specialization of `monad_map` to `reader_t` that allows `ρ` to be inferred. -/
class monad_reader_functor (ρ ρ' : out_param (Type u)) (m : out_param (Type u → Type v)) (n n' : Type u → Type w) :=
[functor {} : monad_functor_t (reader_t ρ m) (reader_t ρ' m) n n']

attribute [instance] monad_reader_functor.mk
local attribute [instance] monad_reader_functor.functor

def with_reader_t {ρ ρ' m} [monad m] {α} (f : ρ' → ρ) : reader_t ρ m α → reader_t ρ' m α :=
λ x, ⟨λ r, x.run (f r)⟩

/-- Embed a computation, modifying the top-most environment (possibly including its type) in its monad stack. -/
def with_reader {ρ ρ'} {m n n'} [monad m] [monad_reader_functor ρ ρ' m n n'] {α : Type u} (f : ρ' → ρ) : n α → n' α :=
monad_map $ λ α, (with_reader_t f : reader_t ρ m α → reader_t ρ' m α)


instance (ρ : Type u) (m out) [monad_run out m] : monad_run (λ α, ρ → out α) (reader_t ρ m) :=
⟨λ α x, run ∘ x.run⟩
