/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Vector.Lemmas
import Init.Data.Vector.Attach
import Init.Data.Array.Monadic
import Init.Control.Lawful.Lemmas

/-!
# Lemmas about `Vector.forIn'` and `Vector.forIn`.
-/

namespace Vector

open Nat

/-! ## Monadic operations -/

theorem map_toArray_inj [Monad m] [LawfulMonad m] [Nonempty α]
    {v₁ : m (Vector α n)} {v₂ : m (Vector α n)} (w : toArray <$> v₁ = toArray <$> v₂) :
    v₁ = v₂ := by
  apply map_inj_of_inj ?_ w
  simp

/-! ### mapM -/

@[congr] theorem mapM_congr [Monad m] {as bs : Vector α n} (w : as = bs)
    {f : α → m β} :
    as.mapM f = bs.mapM f := by
  subst w
  simp

@[simp] theorem mapM_mk_empty [Monad m] (f : α → m β)  :
    (mk #[] rfl).mapM f = pure #v[] := by
  unfold mapM
  unfold mapM.go
  simp

-- The `[Nonempty β]` hypothesis should be avoidable by unfolding `mapM` directly.
@[simp] theorem mapM_append [Monad m] [LawfulMonad m] [Nonempty β]
    (f : α → m β) {l₁ : Vector α n} {l₂ : Vector α n'} :
    (l₁ ++ l₂).mapM f = (return (← l₁.mapM f) ++ (← l₂.mapM f)) := by
  apply map_toArray_inj
  suffices toArray <$> (l₁ ++ l₂).mapM f = (return (← toArray <$> l₁.mapM f) ++ (← toArray <$> l₂.mapM f)) by
    rw [this]
    simp only [bind_pure_comp, Functor.map_map, bind_map_left, map_bind, toArray_append]
  simp

/-! ### foldlM and foldrM -/

theorem foldlM_map [Monad m] (f : β₁ → β₂) (g : α → β₂ → m α) (l : Vector β₁ n) (init : α) :
    (l.map f).foldlM g init = l.foldlM (fun x y => g x (f y)) init := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldlM_map]

theorem foldrM_map [Monad m] [LawfulMonad m] (f : β₁ → β₂) (g : β₂ → α → m α) (l : Vector β₁ n)
    (init : α) : (l.map f).foldrM g init = l.foldrM (fun x y => g (f x) y) init := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldrM_map]

theorem foldlM_filterMap [Monad m] [LawfulMonad m] (f : α → Option β) (g : γ → β → m γ) (l : Vector α n) (init : γ) :
    (l.filterMap f).foldlM g init =
      l.foldlM (fun x y => match f y with | some b => g x b | none => pure x) init := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldlM_filterMap]
  rfl

theorem foldrM_filterMap [Monad m] [LawfulMonad m] (f : α → Option β) (g : β → γ → m γ) (l : Vector α n) (init : γ) :
    (l.filterMap f).foldrM g init =
      l.foldrM (fun x y => match f x with | some b => g b y | none => pure y) init := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldrM_filterMap]
  rfl

theorem foldlM_filter [Monad m] [LawfulMonad m] (p : α → Bool) (g : β → α → m β) (l : Vector α n) (init : β) :
    (l.filter p).foldlM g init =
      l.foldlM (fun x y => if p y then g x y else pure x) init := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldlM_filter]

theorem foldrM_filter [Monad m] [LawfulMonad m] (p : α → Bool) (g : α → β → m β) (l : Vector α n) (init : β) :
    (l.filter p).foldrM g init =
      l.foldrM (fun x y => if p x then g x y else pure y) init := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldrM_filter]

@[simp] theorem foldlM_attachWith [Monad m]
    (l : Vector α n) {q : α → Prop} (H : ∀ a, a ∈ l → q a) {f : β → { x // q x} → m β} {b} :
    (l.attachWith q H).foldlM f b = l.attach.foldlM (fun b ⟨a, h⟩ => f b ⟨a, H _ h⟩) b := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldlM_map]

@[simp] theorem foldrM_attachWith [Monad m] [LawfulMonad m]
    (l : Vector α n) {q : α → Prop} (H : ∀ a, a ∈ l → q a) {f : { x // q x} → β → m β} {b} :
    (l.attachWith q H).foldrM f b = l.attach.foldrM (fun a acc => f ⟨a.1, H _ a.2⟩ acc) b := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldrM_map]

/-! ### forM -/

@[congr] theorem forM_congr [Monad m] {as bs : Vector α n} (w : as = bs)
    {f : α → m PUnit} :
    forM as f = forM bs f := by
  cases as <;> cases bs
  simp_all

@[simp] theorem forM_append [Monad m] [LawfulMonad m] (l₁ : Vector α n) (l₂ : Vector α n') (f : α → m PUnit) :
    forM (l₁ ++ l₂) f = (do forM l₁ f; forM l₂ f) := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, rfl⟩
  simp

@[simp] theorem forM_map [Monad m] [LawfulMonad m] (l : Vector α n) (g : α → β) (f : β → m PUnit) :
    forM (l.map g) f = forM l (fun a => f (g a)) := by
  cases l
  simp

/-! ### forIn' -/

@[congr] theorem forIn'_congr [Monad m] {as bs : Vector α n} (w : as = bs)
    {b b' : β} (hb : b = b')
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)}
    (h : ∀ a m b, f a (by simpa [w] using m) b = g a m b) :
    forIn' as b f = forIn' bs b' g := by
  cases as <;> cases bs
  simp only [eq_mk, mem_mk, forIn'_mk] at w h ⊢
  exact Array.forIn'_congr w hb h

/--
We can express a for loop over a vector as a fold,
in which whenever we reach `.done b` we keep that value through the rest of the fold.
-/
theorem forIn'_eq_foldlM [Monad m] [LawfulMonad m]
    (l : Vector α n) (f : (a : α) → a ∈ l → β → m (ForInStep β)) (init : β) :
    forIn' l init f = ForInStep.value <$>
      l.attach.foldlM (fun b ⟨a, m⟩ => match b with
        | .yield b => f a m b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.forIn'_eq_foldlM]
  rfl

/-- We can express a for loop over a vector which always yields as a fold. -/
@[simp] theorem forIn'_yield_eq_foldlM [Monad m] [LawfulMonad m]
    (l : Vector α n) (f : (a : α) → a ∈ l → β → m γ) (g : (a : α) → a ∈ l → β → γ → β) (init : β) :
    forIn' l init (fun a m b => (fun c => .yield (g a m b c)) <$> f a m b) =
      l.attach.foldlM (fun b ⟨a, m⟩ => g a m b <$> f a m b) init := by
  rcases l with ⟨l, rfl⟩
  simp

theorem forIn'_pure_yield_eq_foldl [Monad m] [LawfulMonad m]
    (l : Vector α n) (f : (a : α) → a ∈ l → β → β) (init : β) :
    forIn' l init (fun a m b => pure (.yield (f a m b))) =
      pure (f := m) (l.attach.foldl (fun b ⟨a, h⟩ => f a h b) init) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.forIn'_pure_yield_eq_foldl, Array.foldl_map]

@[simp] theorem forIn'_yield_eq_foldl
    (l : Vector α n) (f : (a : α) → a ∈ l → β → β) (init : β) :
    forIn' (m := Id) l init (fun a m b => .yield (f a m b)) =
      l.attach.foldl (fun b ⟨a, h⟩ => f a h b) init := by
  cases l
  simp [List.foldl_map]

@[simp] theorem forIn'_map [Monad m] [LawfulMonad m]
    (l : Vector α n) (g : α → β) (f : (b : β) → b ∈ l.map g → γ → m (ForInStep γ)) :
    forIn' (l.map g) init f = forIn' l init fun a h y => f (g a) (mem_map_of_mem g h) y := by
  cases l
  simp

/--
We can express a for loop over a vector as a fold,
in which whenever we reach `.done b` we keep that value through the rest of the fold.
-/
theorem forIn_eq_foldlM [Monad m] [LawfulMonad m]
    (f : α → β → m (ForInStep β)) (init : β) (l : Vector α n) :
    forIn l init f = ForInStep.value <$>
      l.foldlM (fun b a => match b with
        | .yield b => f a b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.forIn_eq_foldlM]
  rfl

/-- We can express a for loop over a vector which always yields as a fold. -/
@[simp] theorem forIn_yield_eq_foldlM [Monad m] [LawfulMonad m]
    (l : Vector α n) (f : α → β → m γ) (g : α → β → γ → β) (init : β) :
    forIn l init (fun a b => (fun c => .yield (g a b c)) <$> f a b) =
      l.foldlM (fun b a => g a b <$> f a b) init := by
  cases l
  simp

theorem forIn_pure_yield_eq_foldl [Monad m] [LawfulMonad m]
    (l : Vector α n) (f : α → β → β) (init : β) :
    forIn l init (fun a b => pure (.yield (f a b))) =
      pure (f := m) (l.foldl (fun b a => f a b) init) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.forIn_pure_yield_eq_foldl, Array.foldl_map]

@[simp] theorem forIn_yield_eq_foldl
    (l : Vector α n) (f : α → β → β) (init : β) :
    forIn (m := Id) l init (fun a b => .yield (f a b)) =
      l.foldl (fun b a => f a b) init := by
  cases l
  simp

@[simp] theorem forIn_map [Monad m] [LawfulMonad m]
    (l : Vector α n) (g : α → β) (f : β → γ → m (ForInStep γ)) :
    forIn (l.map g) init f = forIn l init fun a y => f (g a) y := by
  cases l
  simp

end Vector
