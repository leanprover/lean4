/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The reader monad transformer for passing immutable state.
-/

prelude
import init.category.lift init.category.id
universes u v w

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
end
end reader_t


/-- A specialization of `monad_lift` to `reader_t` that allows `ρ` to be inferred. -/
class monad_reader_lift (ρ : out_param (Type u)) (m : out_param (Type u → Type v)) (n : Type u → Type w) :=
[has_lift : has_monad_lift_t (reader_t ρ m) n]

attribute [instance] monad_reader_lift.mk
local attribute [instance] monad_reader_lift.has_lift

def monad_reader_lift.read {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w} [monad m] [monad_reader_lift ρ m n] : n ρ :=
@monad_lift _ _ _ _ (reader_t.read : reader_t ρ m _)
export monad_reader_lift (read)


/-- A specialization of `monad_map` to `reader_t` that allows `r` to be inferred. -/
class monad_reader_functor (ρ ρ' : out_param (Type u)) (m : out_param (Type u → Type v)) (n n' : Type u → Type w) :=
[functor {} : monad_functor_t (reader_t ρ m) (reader_t ρ' m) n n']

attribute [instance] monad_reader_functor.mk
local attribute [instance] monad_reader_functor.functor

def with_reader_t {ρ ρ' m} [monad m] {α} (f : ρ' → ρ) : reader_t ρ m α → reader_t ρ' m α :=
λ x, ⟨λ r, x.run (f r)⟩

def with_reader {ρ ρ'} {m n n'} [monad m] [monad_reader_functor ρ ρ' m n n'] {α : Type u} (f : ρ' → ρ) : n α → n' α :=
monad_map $ λ α, (with_reader_t f : reader_t ρ m α → reader_t ρ' m α)


instance (ρ : Type u) (m out) [monad_run out m] : monad_run (λ α, ρ → out α) (reader_t ρ m) :=
⟨λ α x, run ∘ x.run, λ α a, reader_t.mk (unrun ∘ a)⟩
