/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude

import Init.Data.Option.Attach
import Init.Control.Lawful.Basic

namespace Option

@[congr] theorem forIn'_congr [Monad m] [LawfulMonad m]{as bs : Option α} (w : as = bs)
    {b b' : β} (hb : b = b')
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)}
    (h : ∀ a m b, f a (by simpa [w] using m) b = g a m b) :
    forIn' as b f = forIn' bs b' g := by
  cases as <;> cases bs
  · simp [hb]
  · simp at w
  · simp at w
  · simp only [some.injEq] at w
    subst w
    simp [hb, h]

theorem forIn'_eq_pelim [Monad m] [LawfulMonad m]
    (o : Option α) (f : (a : α) → a ∈ o → β → m (ForInStep β)) (b : β) :
    forIn' o b f =
      o.pelim (pure b) (fun a h => ForInStep.value <$> f a h b) := by
  cases o <;> simp

@[simp] theorem forIn'_yield_eq_pelim [Monad m] [LawfulMonad m] (o : Option α)
    (f : (a : α) → a ∈ o → β → m γ) (g : (a : α) → a ∈ o → β → γ → β) (b : β) :
    forIn' o b (fun a m b => (fun c => .yield (g a m b c)) <$> f a m b) =
      o.pelim (pure b) (fun a h => g a h b <$> f a h b) := by
  cases o <;> simp

theorem forIn'_pure_yield_eq_pelim [Monad m] [LawfulMonad m]
    (o : Option α) (f : (a : α) → a ∈ o → β → β) (b : β) :
    forIn' o b (fun a m b => pure (.yield (f a m b))) =
      pure (f := m) (o.pelim b (fun a h => f a h b)) := by
  cases o <;> simp

@[simp] theorem forIn'_id_yield_eq_pelim
    (o : Option α) (f : (a : α) → a ∈ o → β → β) (b : β) :
    forIn' (m := Id) o b (fun a m b => .yield (f a m b)) =
      o.pelim b (fun a h => f a h b) := by
  cases o <;> simp

theorem forIn_eq_elim [Monad m] [LawfulMonad m]
    (o : Option α) (f : (a : α) → β → m (ForInStep β)) (b : β) :
    forIn o b f =
      o.elim (pure b) (fun a => ForInStep.value <$> f a b) := by
  cases o <;> simp

@[simp] theorem forIn_yield_eq_elim [Monad m] [LawfulMonad m] (o : Option α)
    (f : (a : α) → β → m γ) (g : (a : α) → β → γ → β) (b : β) :
    forIn o b (fun a b => (fun c => .yield (g a b c)) <$> f a b) =
      o.elim (pure b) (fun a => g a b <$> f a b) := by
  cases o <;> simp

theorem forIn_pure_yield_eq_elim [Monad m] [LawfulMonad m]
    (o : Option α) (f : (a : α) → β → β) (b : β) :
    forIn o b (fun a b => pure (.yield (f a b))) =
      pure (f := m) (o.elim b (fun a => f a b)) := by
  cases o <;> simp

@[simp] theorem forIn_id_yield_eq_elim
    (o : Option α) (f : (a : α) → β → β) (b : β) :
    forIn (m := Id) o b (fun a b => .yield (f a b)) =
      o.elim b (fun a => f a b) := by
  cases o <;> simp

end Option
