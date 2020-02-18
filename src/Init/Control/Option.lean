/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Control.Alternative
import Init.Control.Lift
import Init.Control.Except

universes u v

def OptionT (m : Type u → Type v) (α : Type u) : Type v :=
m (Option α)

@[inline] def OptionT.run {m : Type u → Type v} {α : Type u} (x : OptionT m α) : m (Option α) :=
x

namespace OptionT
  variables {m : Type u → Type v} [Monad m] {α β : Type u}

  @[inline] protected def bind (ma : OptionT m α) (f : α → OptionT m β) : OptionT m β :=
  (do {
    a? ← ma;
    match a? with
    | some a => f a
    | none   => pure none
  } : m (Option β))

  @[inline] protected def pure (a : α) : OptionT m α :=
  (pure (some a) : m (Option α))

  instance : Monad (OptionT m) :=
  { pure := @OptionT.pure _ _, bind := @OptionT.bind _ _ }

  @[inline] protected def orelse (ma : OptionT m α) (mb : OptionT m α) : OptionT m α :=
  (do { a? ← ma;
        match a? with
        | some a => pure (some a)
        | _      => mb } : m (Option α))

  @[inline] protected def fail : OptionT m α :=
  (pure none : m (Option α))

  instance : Alternative (OptionT m) :=
  { failure := @OptionT.fail m _,
    orelse  := @OptionT.orelse m _,
    ..OptionT.Monad }

  @[inline] protected def lift (ma : m α) : OptionT m α :=
  (some <$> ma : m (Option α))

  instance : HasMonadLift m (OptionT m) :=
  ⟨@OptionT.lift _ _⟩

  @[inline] protected def monadMap {m'} [Monad m'] {α} (f : ∀ {α}, m α → m' α) : OptionT m α → OptionT m' α :=
  fun x => f x

  instance (m') [Monad m'] : MonadFunctor m m' (OptionT m) (OptionT m') :=
  ⟨fun α => OptionT.monadMap⟩

  @[inline] protected def catch (ma : OptionT m α) (handle : Unit → OptionT m α) : OptionT m α :=
  (do { some a ← ma | (handle ());
        pure a } : m (Option α))

  instance : MonadExcept Unit (OptionT m) :=
  { throw := fun _ _ => OptionT.fail, catch := @OptionT.catch _ _ }

  instance (m out) [MonadRun out m] : MonadRun (fun α => out (Option α)) (OptionT m) :=
  ⟨fun α => MonadRun.run⟩
end OptionT
