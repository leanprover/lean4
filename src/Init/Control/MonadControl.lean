/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura

See: https://lexi-lambda.github.io/blog/2019/09/07/demystifying-monadbasecontrol/
-/
prelude
import Init.Control.Lift

universes u v w

class MonadControl (m : Type u → Type v) (n : Type u → Type w) :=
(stM : Type u → Type u)
(liftWith {α : Type u} : ((∀ {β}, n β → m (stM β)) → m α) → n α)
(restoreM {α : Type u} : m (stM α) → n α)

class MonadControlT (m : Type u → Type v) (n : Type u → Type w) :=
(stM : Type u → Type u)
(liftWith {α : Type u} : ((∀ {β}, n β → m (stM β)) → m α) → n α)
(restoreM {α : Type u} : stM α → n α)

export MonadControlT (stM liftWith restoreM)

-- Helper abbreviations for writing `monadControlTrans`
private abbrev liftWithB := @MonadControl.liftWith
private abbrev restoreB  := @MonadControl.restoreM
private abbrev liftWithT := @MonadControlT.liftWith
private abbrev restoreT  := @MonadControlT.restoreM

instance monadControlTrans (m n o) [MonadControlT m n] [MonadControl n o] : MonadControlT m o := {
  stM      := fun α   => MonadControlT.stM m n (MonadControl.stM n o α),
  liftWith := fun α f => liftWithB fun x₂ => liftWithT fun x₁ => f fun β => x₁ ∘ x₂,
  restoreM := fun α   => restoreB ∘ restoreT }

instance monadControlRefl (m : Type u → Type v) [HasPure m] : MonadControlT m m := {
  stM      := fun α => α,
  liftWith := fun α f => f fun β x => x,
  restoreM := fun α x => pure x }

@[inline]
def controlAt (m : Type u → Type v) {n : Type u → Type w} [MonadControlT m n] [HasBind n] {α : Type u}
    (f : (∀ {β}, n β → m (stM m n β)) → m (stM m n α)) : n α :=
liftWith f >>= restoreM

@[inline]
def control {m : Type u → Type v} {n : Type u → Type w} [MonadControlT m n] [HasBind n] {α : Type u}
    (f : (∀ {β}, n β → m (stM m n β)) → m (stM m n α)) : n α :=
controlAt m f
