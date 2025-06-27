/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude

import all Init.Data.Option.Instances
import Init.Data.Option.Attach
import Init.Control.Lawful.Basic

namespace Option

@[simp, grind] theorem bindM_none [Pure m] (f : α → m (Option β)) : none.bindM f = pure none := rfl
@[simp, grind] theorem bindM_some [Pure m] (a) (f : α → m (Option β)) : (some a).bindM f = f a := by
  simp [Option.bindM]

-- We simplify `Option.forM` to `forM`.
@[simp] theorem forM_eq_forM [Monad m] : @Option.forM m α _ = forM := rfl

@[simp, grind] theorem forM_none [Monad m] (f : α → m PUnit) :
    forM none f = pure .unit := rfl

@[simp, grind] theorem forM_some [Monad m] (f : α → m PUnit) (a : α) :
    forM (some a) f = f a := rfl

@[simp, grind] theorem forM_map [Monad m] [LawfulMonad m] (o : Option α) (g : α → β) (f : β → m PUnit) :
    forM (o.map g) f = forM o (fun a => f (g a)) := by
  cases o <;> simp

theorem forM_join [Monad m] [LawfulMonad m] (o : Option (Option α)) (f : α → m PUnit) :
    forM o.join f = forM o (forM · f) := by
  cases o <;> simp

@[simp, grind] theorem forIn'_none [Monad m] (b : β) (f : (a : α) → a ∈ none → β → m (ForInStep β)) :
    forIn' none b f = pure b := by
  rfl

@[simp, grind] theorem forIn'_some [Monad m] [LawfulMonad m] (a : α) (b : β) (f : (a' : α) → a' ∈ some a → β → m (ForInStep β)) :
    forIn' (some a) b f = bind (f a rfl b) (fun r => pure (ForInStep.value r)) := by
  simp only [forIn', bind_pure_comp]
  rw [map_eq_pure_bind]
  congr
  funext x
  split <;> simp

@[simp, grind] theorem forIn_none [Monad m] (b : β) (f : α → β → m (ForInStep β)) :
    forIn none b f = pure b := by
  rfl

@[simp, grind] theorem forIn_some [Monad m] [LawfulMonad m] (a : α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn (some a) b f = bind (f a b) (fun r => pure (ForInStep.value r)) := by
  simp only [forIn, forIn', bind_pure_comp]
  rw [map_eq_pure_bind]
  congr
  funext x
  split <;> simp

@[congr] theorem forIn'_congr [Monad m] [LawfulMonad m] {as bs : Option α} (w : as = bs)
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

@[simp] theorem forIn'_pure_yield_eq_pelim [Monad m] [LawfulMonad m]
    (o : Option α) (f : (a : α) → a ∈ o → β → β) (b : β) :
    forIn' o b (fun a m b => pure (.yield (f a m b))) =
      pure (f := m) (o.pelim b (fun a h => f a h b)) := by
  cases o <;> simp

@[simp] theorem idRun_forIn'_yield_eq_pelim
    (o : Option α) (f : (a : α) → a ∈ o → β → Id β) (b : β) :
    (forIn' o b (fun a m b => .yield <$> f a m b)).run =
      o.pelim b (fun a h => f a h b |>.run) :=
  forIn'_pure_yield_eq_pelim _ _ _

@[deprecated idRun_forIn'_yield_eq_pelim (since := "2025-05-21")]
theorem forIn'_id_yield_eq_pelim
    (o : Option α) (f : (a : α) → a ∈ o → β → β) (b : β) :
    forIn' (m := Id) o b (fun a m b => .yield (f a m b)) =
      o.pelim b (fun a h => f a h b) :=
  forIn'_pure_yield_eq_pelim _ _ _

@[simp, grind] theorem forIn'_map [Monad m] [LawfulMonad m]
    (o : Option α) (g : α → β) (f : (b : β) → b ∈ o.map g → γ → m (ForInStep γ)) :
    forIn' (o.map g) init f = forIn' o init fun a h y => f (g a) (mem_map_of_mem g h) y := by
  cases o <;> simp

theorem forIn'_join [Monad m] [LawfulMonad m] (b : β) (o : Option (Option α))
    (f : (a : α) → a ∈ o.join → β → m (ForInStep β)) :
    forIn' o.join b f = forIn' o b (fun o' ho' b => ForInStep.yield <$> forIn' o' b (fun a ha b' => f a (by simp_all) b')) := by
  cases o with
  | none => simp
  | some a => simpa using forIn'_congr rfl rfl (by simp)

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

@[simp] theorem forIn_pure_yield_eq_elim [Monad m] [LawfulMonad m]
    (o : Option α) (f : (a : α) → β → β) (b : β) :
    forIn o b (fun a b => pure (.yield (f a b))) =
      pure (f := m) (o.elim b (fun a => f a b)) := by
  cases o <;> simp

@[simp] theorem idRun_forIn_yield_eq_elim
    (o : Option α) (f : (a : α) → β → Id β) (b : β) :
    (forIn o b (fun a b => .yield <$> f a b)).run =
      o.elim b (fun a => f a b |>.run) :=
  forIn_pure_yield_eq_elim _ _ _

@[deprecated idRun_forIn_yield_eq_elim (since := "2025-05-21")]
theorem forIn_id_yield_eq_elim
    (o : Option α) (f : (a : α) → β → β) (b : β) :
    forIn (m := Id) o b (fun a b => .yield (f a b)) =
      o.elim b (fun a => f a b) :=
  forIn_pure_yield_eq_elim _ _ _

@[simp, grind] theorem forIn_map [Monad m] [LawfulMonad m]
    (o : Option α) (g : α → β) (f : β → γ → m (ForInStep γ)) :
    forIn (o.map g) init f = forIn o init fun a y => f (g a) y := by
  cases o <;> simp

theorem forIn_join [Monad m] [LawfulMonad m]
    (o : Option (Option α)) (f : α → β → m (ForInStep β)) :
    forIn o.join init f = forIn o init (fun o' b => ForInStep.yield <$> forIn o' b f) := by
  cases o <;> simp

@[simp, grind =] theorem elimM_pure [Monad m] [LawfulMonad m] (x : Option α) (y : m β) (z : α → m β) :
    Option.elimM (pure x : m (Option α)) y z = x.elim y z := by
  simp [Option.elimM]

@[simp, grind =] theorem elimM_bind [Monad m] [LawfulMonad m] (x : m α) (f : α → m (Option β))
    (y : m γ) (z : β → m γ) : Option.elimM (x >>= f) y z = (do Option.elimM (f (← x)) y z) := by
  simp [Option.elimM]

@[simp, grind =] theorem elimM_map [Monad m] [LawfulMonad m] (x : m α) (f : α → Option β)
    (y : m γ) (z : β → m γ) : Option.elimM (f <$> x) y z = (do Option.elim (f (← x)) y z) := by
  simp [Option.elimM]

@[simp, grind =] theorem tryCatch_eq_or (o : Option α) (alternative : Unit → Option α) :
    tryCatch o alternative = o.or (alternative ()) := by cases o <;> rfl

@[simp, grind =] theorem throw_eq_none : throw () = (none : Option α) := rfl

@[simp, grind =] theorem filterM_none [Applicative m] (p : α → m Bool) :
    none.filterM p = pure none := rfl
@[grind =] theorem filterM_some [Applicative m] (p : α → m Bool) (a : α) :
    (some a).filterM p = (fun b => if b then some a else none) <$> p a := rfl

theorem sequence_join [Applicative m] [LawfulApplicative m] {o : Option (Option (m α))} :
    o.join.sequence = join <$> sequence (o.map sequence) := by
  cases o <;> simp

theorem bindM_join [Pure m] {f : α → m (Option β)} {o : Option (Option α)} :
    o.join.bindM f = o.bindM (·.bindM f) := by
  cases o <;> simp

theorem mapM_join [Applicative m] [LawfulApplicative m] {f : α → m β} {o : Option (Option α)} :
    o.join.mapM f = join <$> o.mapM (Option.mapM f) := by
  cases o <;> simp

theorem mapM_guard [Applicative m] {x : α} {p : α → Bool} {f : α → m β} :
    (guard p x).mapM f = if p x then some <$> f x else pure none := by
  simp only [guard_eq_ite]
  split <;> simp

end Option
