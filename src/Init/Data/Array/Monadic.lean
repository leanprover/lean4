/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.Array.Attach
import Init.Data.List.Monadic

/-!
# Lemmas about `Array.forIn'` and `Array.forIn`.
-/

namespace Array

open Nat

/-! ## Monadic operations -/

/-! ### mapM -/

theorem mapM_eq_foldlM_push [Monad m] [LawfulMonad m] (f : α → m β) (l : Array α) :
    mapM f l = l.foldlM (fun acc a => return (acc.push (← f a))) #[] := by
  rcases l with ⟨l⟩
  simp only [List.mapM_toArray, bind_pure_comp, size_toArray, List.foldlM_toArray']
  rw [List.mapM_eq_reverse_foldlM_cons]
  simp only [bind_pure_comp, Functor.map_map]
  suffices ∀ (k), (fun a => a.reverse.toArray) <$> List.foldlM (fun acc a => (fun a => a :: acc) <$> f a) k l =
      List.foldlM (fun acc a => acc.push <$> f a) k.reverse.toArray l by
    exact this []
  intro k
  induction l generalizing k with
  | nil => simp
  | cons a as ih =>
    simp [ih, List.foldlM_cons]

/-! ### foldlM and foldrM -/

theorem foldlM_map [Monad m] (f : β₁ → β₂) (g : α → β₂ → m α) (l : Array β₁) (init : α) :
    (l.map f).foldlM g init = l.foldlM (fun x y => g x (f y)) init := by
  cases l
  rw [List.map_toArray] -- Why doesn't this fire via `simp`?
  simp [List.foldlM_map]

theorem foldrM_map [Monad m] [LawfulMonad m] (f : β₁ → β₂) (g : β₂ → α → m α) (l : Array β₁)
    (init : α) : (l.map f).foldrM g init = l.foldrM (fun x y => g (f x) y) init := by
  cases l
  rw [List.map_toArray] -- Why doesn't this fire via `simp`?
  simp [List.foldrM_map]

theorem foldlM_filterMap [Monad m] [LawfulMonad m] (f : α → Option β) (g : γ → β → m γ) (l : Array α) (init : γ) :
    (l.filterMap f).foldlM g init =
      l.foldlM (fun x y => match f y with | some b => g x b | none => pure x) init := by
  cases l
  rw [List.filterMap_toArray] -- Why doesn't this fire via `simp`?
  simp [List.foldlM_filterMap]
  rfl

theorem foldrM_filterMap [Monad m] [LawfulMonad m] (f : α → Option β) (g : β → γ → m γ) (l : Array α) (init : γ) :
    (l.filterMap f).foldrM g init =
      l.foldrM (fun x y => match f x with | some b => g b y | none => pure y) init := by
  cases l
  rw [List.filterMap_toArray] -- Why doesn't this fire via `simp`?
  simp [List.foldrM_filterMap]
  rfl

theorem foldlM_filter [Monad m] [LawfulMonad m] (p : α → Bool) (g : β → α → m β) (l : Array α) (init : β) :
    (l.filter p).foldlM g init =
      l.foldlM (fun x y => if p y then g x y else pure x) init := by
  cases l
  rw [List.filter_toArray] -- Why doesn't this fire via `simp`?
  simp [List.foldlM_filter]

theorem foldrM_filter [Monad m] [LawfulMonad m] (p : α → Bool) (g : α → β → m β) (l : Array α) (init : β) :
    (l.filter p).foldrM g init =
      l.foldrM (fun x y => if p x then g x y else pure y) init := by
  cases l
  rw [List.filter_toArray] -- Why doesn't this fire via `simp`?
  simp [List.foldrM_filter]

/-! ### forM -/

@[congr] theorem forM_congr [Monad m] {as bs : Array α} (w : as = bs)
    {f : α → m PUnit} :
    as.forM f = bs.forM f := by
  cases as <;> cases bs
  simp_all

@[simp] theorem forM_map [Monad m] [LawfulMonad m] (l : Array α) (g : α → β) (f : β → m PUnit) :
    (l.map g).forM f = l.forM (fun a => f (g a)) := by
  cases l
  simp

/-! ### forIn' -/

@[congr] theorem forIn'_congr [Monad m] {as bs : Array α} (w : as = bs)
    {b b' : β} (hb : b = b')
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)}
    (h : ∀ a m b, f a (by simpa [w] using m) b = g a m b) :
    forIn' as b f = forIn' bs b' g := by
  cases as <;> cases bs
  simp only [mk.injEq, mem_toArray, List.forIn'_toArray] at w h ⊢
  exact List.forIn'_congr w hb h

/--
We can express a for loop over an array as a fold,
in which whenever we reach `.done b` we keep that value through the rest of the fold.
-/
theorem forIn'_eq_foldlM [Monad m] [LawfulMonad m]
    (l : Array α) (f : (a : α) → a ∈ l → β → m (ForInStep β)) (init : β) :
    forIn' l init f = ForInStep.value <$>
      l.attach.foldlM (fun b ⟨a, m⟩ => match b with
        | .yield b => f a m b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  cases l
  rw [List.attach_toArray] -- Why doesn't this fire via `simp`?
  simp only [List.forIn'_toArray, List.forIn'_eq_foldlM, List.attachWith_mem_toArray, size_toArray,
    List.length_map, List.length_attach, List.foldlM_toArray', List.foldlM_map]
  congr

/-- We can express a for loop over an array which always yields as a fold. -/
@[simp] theorem forIn'_yield_eq_foldlM [Monad m] [LawfulMonad m]
    (l : Array α) (f : (a : α) → a ∈ l → β → m γ) (g : (a : α) → a ∈ l → β → γ → β) (init : β) :
    forIn' l init (fun a m b => (fun c => .yield (g a m b c)) <$> f a m b) =
      l.attach.foldlM (fun b ⟨a, m⟩ => g a m b <$> f a m b) init := by
  cases l
  rw [List.attach_toArray] -- Why doesn't this fire via `simp`?
  simp [List.foldlM_map]

theorem forIn'_pure_yield_eq_foldl [Monad m] [LawfulMonad m]
    (l : Array α) (f : (a : α) → a ∈ l → β → β) (init : β) :
    forIn' l init (fun a m b => pure (.yield (f a m b))) =
      pure (f := m) (l.attach.foldl (fun b ⟨a, h⟩ => f a h b) init) := by
  cases l
  simp [List.forIn'_pure_yield_eq_foldl, List.foldl_map]

@[simp] theorem forIn'_yield_eq_foldl
    (l : Array α) (f : (a : α) → a ∈ l → β → β) (init : β) :
    forIn' (m := Id) l init (fun a m b => .yield (f a m b)) =
      l.attach.foldl (fun b ⟨a, h⟩ => f a h b) init := by
  cases l
  simp [List.foldl_map]

@[simp] theorem forIn'_map [Monad m] [LawfulMonad m]
    (l : Array α) (g : α → β) (f : (b : β) → b ∈ l.map g → γ → m (ForInStep γ)) :
    forIn' (l.map g) init f = forIn' l init fun a h y => f (g a) (mem_map_of_mem g h) y := by
  cases l
  simp

/--
We can express a for loop over an array as a fold,
in which whenever we reach `.done b` we keep that value through the rest of the fold.
-/
theorem forIn_eq_foldlM [Monad m] [LawfulMonad m]
    (f : α → β → m (ForInStep β)) (init : β) (l : Array α) :
    forIn l init f = ForInStep.value <$>
      l.foldlM (fun b a => match b with
        | .yield b => f a b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  cases l
  simp only [List.forIn_toArray, List.forIn_eq_foldlM, size_toArray, List.foldlM_toArray']
  congr

/-- We can express a for loop over an array which always yields as a fold. -/
@[simp] theorem forIn_yield_eq_foldlM [Monad m] [LawfulMonad m]
    (l : Array α) (f : α → β → m γ) (g : α → β → γ → β) (init : β) :
    forIn l init (fun a b => (fun c => .yield (g a b c)) <$> f a b) =
      l.foldlM (fun b a => g a b <$> f a b) init := by
  cases l
  simp [List.foldlM_map]

theorem forIn_pure_yield_eq_foldl [Monad m] [LawfulMonad m]
    (l : Array α) (f : α → β → β) (init : β) :
    forIn l init (fun a b => pure (.yield (f a b))) =
      pure (f := m) (l.foldl (fun b a => f a b) init) := by
  cases l
  simp [List.forIn_pure_yield_eq_foldl, List.foldl_map]

@[simp] theorem forIn_yield_eq_foldl
    (l : Array α) (f : α → β → β) (init : β) :
    forIn (m := Id) l init (fun a b => .yield (f a b)) =
      l.foldl (fun b a => f a b) init := by
  cases l
  simp [List.foldl_map]

@[simp] theorem forIn_map [Monad m] [LawfulMonad m]
    (l : Array α) (g : α → β) (f : β → γ → m (ForInStep γ)) :
    forIn (l.map g) init f = forIn l init fun a y => f (g a) y := by
  cases l
  simp

end Array
