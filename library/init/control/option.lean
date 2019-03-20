/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.alternative init.control.lift init.control.except

universes u v

def optionT (m : Type u → Type v) (α : Type u) : Type v :=
m (option α)

@[inline] def optionT.run {m : Type u → Type v} {α : Type u} (x : optionT m α) : m (option α) :=
x

namespace optionT
  variables {m : Type u → Type v} [monad m] {α β : Type u}

  @[inline] protected def bindCont {α β : Type u} (f : α → optionT m β) : option α → m (option β)
  | (some a) := f a
  | none     := pure none

  @[inline] protected def bind (ma : optionT m α) (f : α → optionT m β) : optionT m β :=
  (ma >>= optionT.bindCont f : m (option β))

  @[inline] protected def pure (a : α) : optionT m α :=
  (pure (some a) : m (option α))

  instance : monad (optionT m) :=
  { pure := @optionT.pure _ _, bind := @optionT.bind _ _ }

  protected def orelse (ma : optionT m α) (mb : optionT m α) : optionT m α :=
  (do { some a ← ma | mb,
        pure (some a) } : m (option α))

  @[inline] protected def fail : optionT m α :=
  (pure none : m (option α))

  instance : alternative (optionT m) :=
  { failure := @optionT.fail m _,
    orelse  := @optionT.orelse m _,
    ..optionT.monad }

  @[inline] protected def lift (ma : m α) : optionT m α :=
  (some <$> ma : m (option α))

  instance : hasMonadLift m (optionT m) :=
  ⟨@optionT.lift _ _⟩

  @[inline] protected def monadMap {m'} [monad m'] {α} (f : ∀ {α}, m α → m' α) : optionT m α → optionT m' α :=
  λ x, f x

  instance (m') [monad m'] : monadFunctor m m' (optionT m) (optionT m') :=
  ⟨λ α, optionT.monadMap⟩

  protected def catch (ma : optionT m α) (handle : unit → optionT m α) : optionT m α :=
  (do { some a ← ma | (handle ()),
        pure a } : m (option α))

  instance : monadExcept unit (optionT m) :=
  { throw := λ _ _, optionT.fail, catch := @optionT.catch _ _ }

  instance (m out) [monadRun out m] : monadRun (λ α, out (option α)) (optionT m) :=
  ⟨λ α, monadRun.run⟩
end optionT
