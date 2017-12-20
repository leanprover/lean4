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

class monad_except (ε : out_param (Type u)) (m : Type v → Type w) [monad m] :=
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

  instance monad : monad (except ε) :=
  { map := @map, pure := @return, bind := @bind }
end
end except

structure except_t (ε : Type u) (m : Type u → Type v) [monad m] (α : Type u) : Type v :=
(run : m (except ε α))

attribute [pp_using_anonymous_constructor] except_t

namespace except_t
section
  parameters {ε : Type u} {m : Type u → Type v} [monad m]

  protected def return {α : Type u} (a : α) : except_t ε m α :=
  ⟨pure $ except.ok a⟩

  protected def map {α β : Type u} (f : α → β) (ma : except_t ε m α) : except_t ε m β :=
  ⟨has_map.map f <$> ma.run⟩

  protected def bind {α β : Type u} (ma : except_t ε m α) (f : α → except_t ε m β) : except_t ε m β :=
  ⟨ma.run >>= λ res, match res with
   | except.ok a    := (f a).run
   | except.error e := pure (except.error e)
   end⟩

  protected def lift {α : Type u} (t : m α) : except_t ε m α :=
  ⟨except.ok <$> t⟩

  protected def catch {α : Type u} (ma : except_t ε m α) (handle : ε → except_t ε m α) : except_t ε m α :=
  ⟨ma.run >>= λ res, match res with
   | except.ok a    := pure (except.ok a)
   | except.error e := (handle e).run
   end⟩

  instance : monad (except_t ε m) :=
  { pure := @return, map := @map, bind := @bind }
end

instance (ε : Type u) : monad_transformer (except_t ε) :=
{ is_monad := @except_t.monad ε, monad_lift := @except_t.lift ε }
end except_t

instance (m ε) [monad m] : monad_except ε (except_t ε m) :=
{ throw := λ α, except_t.mk ∘ pure ∘ except.error, catch := @except_t.catch ε _ _ }

def map_except_t {ε m m'} [monad m] [monad m'] {α β} (f : m (except ε α) → m' (except ε β)) : except_t ε m α → except_t ε m' β :=
λ x, ⟨f x.run⟩
