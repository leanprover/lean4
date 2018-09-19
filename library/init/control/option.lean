/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.alternative init.control.lift init.control.except

universes u v

def option_t (m : Type u → Type v) (α : Type u) : Type v :=
m (option α)

@[inline] def option_t.run {m : Type u → Type v} {α : Type u} (x : option_t m α) : m (option α) :=
x

namespace option_t
  variables {m : Type u → Type v} [monad m] {α β : Type u}

  @[inline] protected def bind_cont {α β : Type u} (f : α → option_t m β) : option α → m (option β)
  | (some a) := f a
  | none     := pure none

  @[inline] protected def bind (ma : option_t m α) (f : α → option_t m β) : option_t m β :=
  (ma >>= option_t.bind_cont f : m (option β))

  @[inline] protected def pure (a : α) : option_t m α :=
  (pure (some a) : m (option α))

  instance : monad (option_t m) :=
  { pure := @option_t.pure _ _, bind := @option_t.bind _ _ }

  protected def orelse (ma : option_t m α) (mb : option_t m α) : option_t m α :=
  (do { some a ← ma | mb,
        pure (some a) } : m (option α))

  @[inline] protected def fail : option_t m α :=
  (pure none : m (option α))

  instance : alternative (option_t m) :=
  { failure := @option_t.fail m _,
    orelse  := @option_t.orelse m _,
    ..option_t.monad }

  @[inline] protected def lift (ma : m α) : option_t m α :=
  (some <$> ma : m (option α))

  instance : has_monad_lift m (option_t m) :=
  ⟨@option_t.lift _ _⟩

  @[inline] protected def monad_map {m'} [monad m'] {α} (f : ∀ {α}, m α → m' α) : option_t m α → option_t m' α :=
  λ x, f x

  instance (m') [monad m'] : monad_functor m m' (option_t m) (option_t m') :=
  ⟨λ α, option_t.monad_map⟩

  protected def catch (ma : option_t m α) (handle : unit → option_t m α) : option_t m α :=
  (do { some a ← ma | (handle ()),
        pure a } : m (option α))

  instance : monad_except unit (option_t m) :=
  { throw := λ _ _, option_t.fail, catch := @option_t.catch _ _ }

  instance (m out) [monad_run out m] : monad_run (λ α, out (option α)) (option_t m) :=
  ⟨λ α, monad_run.run⟩
end option_t
