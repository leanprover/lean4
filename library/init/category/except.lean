/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch, Sebastian Ullrich
-/

prelude
import init.category.transformers
universes u v w

inductive except (ε α : Type u)
| error {} : ε → except
| ok {} : α → except

class monad_except (ε : out_param (Type u)) (m : Type v → Type w) :=
(throw {} {α : Type v} : ε → m α)
(catch {} {α : Type v} : m α → (ε → m α) → m α)

export monad_except (throw catch)

namespace except
section
  parameter {ε : Type u}

  protected def return {α : Type u} (a : α) : except ε α :=
  except.ok a

  protected def map {α β : Type u} (f : α → β) : except ε α → except ε β
  | (except.error err) := except.error err
  | (except.ok v) := except.ok $ f v

  protected def bind {α β : Type u} (ma : except ε α) (f : α → except ε β) : except ε β :=
  match ma with
  | (except.error err) := except.error err
  | (except.ok v) := f v
  end
end
end except

structure except_t (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
(run : m (except ε α))

attribute [pp_using_anonymous_constructor] except_t

namespace except_t
section
  parameters {ε : Type u} {m : Type u → Type v} [monad m]

  protected def return {α : Type u} (a : α) : except_t ε m α :=
  ⟨pure $ except.ok a⟩

  protected def bind_cont {α β : Type u} (f : α → except_t ε m β) : except ε α → m (except ε β)
  | (except.ok a)    := (f a).run
  | (except.error e) := pure (except.error e)

  protected def bind {α β : Type u} (ma : except_t ε m α) (f : α → except_t ε m β) : except_t ε m β :=
  ⟨ma.run >>= bind_cont f⟩

  protected def lift {α : Type u} (t : m α) : except_t ε m α :=
  ⟨except.ok <$> t⟩

  protected def catch {α : Type u} (ma : except_t ε m α) (handle : ε → except_t ε m α) : except_t ε m α :=
  ⟨ma.run >>= λ res, match res with
   | except.ok a    := pure (except.ok a)
   | except.error e := (handle e).run
   end⟩

  instance : monad (except_t ε m) :=
  { pure := @return, bind := @bind }
end
end except_t

instance (m ε) [monad m] : monad_except ε (except_t ε m) :=
{ throw := λ α, except_t.mk ∘ pure ∘ except.error, catch := @except_t.catch ε _ _ }

def map_except_t {ε m m'} [monad m] [monad m'] {α} (f : ∀ {α}, m α → m' α) : except_t ε m α → except_t ε m' α :=
λ x, ⟨f x.run⟩

instance (ε m m') [monad m] [monad m'] : monad_functor m m' (except_t ε m) (except_t ε m') :=
⟨@map_except_t ε m m' _ _⟩

instance (ε m out) [monad_run out m] : monad_run (λ α, out (except ε α)) (except_t ε m) :=
⟨λ α, run ∘ except_t.run, λ α, except_t.mk ∘ unrun⟩
