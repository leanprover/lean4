/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

prelude
import init.category.transformers init.category.id
universes u v

class monad_reader (r : out_param (Type u)) (m : Type u → Type v) [monad m] :=
(reader {} {α : Type u} : (r → α) → m α)
(read {} : m r := reader id)
(reader := λ α f, f <$> read)
-- TODO(Sebastian): It's not clear to me how useful this operation is since it cannot change the
-- type of the environment, and we would need something like
-- https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html to lift it
--(with_reader {} {α : Type u} : (r → r) → m α → m α)

export monad_reader (read)

def reader_t (r : Type u) (m : Type u → Type v) [monad m] (α : Type u) : Type (max u v) :=
r → m α

@[reducible] def reader (r : Type u) := reader_t r id

namespace reader_t
section
  variable  {r : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}

  protected def read : reader_t r m r :=
  λ r, pure r

  protected def run : r → reader_t r m α → m α :=
  λ r x, x r

  protected def pure (a : α) : reader_t r m α :=
  λ r, pure a

  protected def bind (x : reader_t r m α) (f : α → reader_t r m β) : reader_t r m β :=
  λ r, do a ← x r,
          f a r

  instance : monad (reader_t r m) :=
  { pure := @reader_t.pure _ _ _, bind := @reader_t.bind _ _ _ }

  protected def lift (a : m α) : reader_t r m α :=
  λ r, a

  instance : monad_transformer (reader_t r) :=
  { is_monad := @reader_t.monad r, monad_lift := @reader_t.lift r }
end
end reader_t

def with_reader_t {r r' m} [monad m] {α} (f : r' → r) : reader_t r m α → reader_t r' m α :=
λ x r, x (f r)

def map_reader_t {r m m'} [monad m] [monad m'] {α β} (f : m α → m' β) : reader_t r m α → reader_t r m' β :=
λ x r, f (x r)

instance (r m) [monad m] : monad_reader r (reader_t r m) :=
{ reader := λ α f, pure ∘ f } --, with_reader := @with_reader_t _ _ _ _ }

instance monad_reader_lift (r m m') [has_monad_lift m m'] [monad m] [monad_reader r m] [monad m'] : monad_reader r m' :=
{ reader := λ α, monad_lift ∘ (monad_reader.reader : _ → m α) }
