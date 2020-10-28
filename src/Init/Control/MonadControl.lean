/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura

See: https://lexi-lambda.github.io/blog/2019/09/07/demystifying-monadbasecontrol/
-/
prelude
import Init.Control.MonadLift

universes u v w

class MonadControl (m : Type u → Type v) (n : Type u → Type w) :=
  (stM      : Type u → Type u)
  (liftWith : {α : Type u} → (({β : Type u} → n β → m (stM β)) → m α) → n α)
  (restoreM : {α : Type u} → m (stM α) → n α)

class MonadControlT (m : Type u → Type v) (n : Type u → Type w) :=
  (stM      : Type u → Type u)
  (liftWith : {α : Type u} → (({β : Type u} → n β → m (stM β)) → m α) → n α)
  (restoreM {α : Type u} : stM α → n α)

export MonadControlT (stM liftWith restoreM)

instance (m n o) [MonadControlT m n] [MonadControl n o] : MonadControlT m o := {
  stM      := fun α => stM m n (MonadControl.stM n o α),
  liftWith := fun f => MonadControl.liftWith fun x₂ => liftWith fun x₁ => f (x₁ ∘ x₂),
  restoreM := MonadControl.restoreM ∘ restoreM
}

instance (m : Type u → Type v) [Pure m] : MonadControlT m m := {
  stM      := fun α => α,
  liftWith := fun f => f fun x => x,
  restoreM := fun x => pure x
}

@[inline]
def controlAt (m : Type u → Type v) {n : Type u → Type w} [s1 : MonadControlT m n] [s2 : Bind n] {α : Type u}
    (f : ({β : Type u} → n β → m (stM m n β)) → m (stM m n α)) : n α :=
  liftWith f >>= restoreM

@[inline]
def control {m : Type u → Type v} {n : Type u → Type w} [MonadControlT m n] [Bind n] {α : Type u}
    (f : ({β : Type u} → n β → m (stM m n β)) → m (stM m n α)) : n α :=
  controlAt m f
