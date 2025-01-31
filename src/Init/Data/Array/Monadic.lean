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

@[simp] theorem mapM_append [Monad m] [LawfulMonad m] (f : α → m β) {l₁ l₂ : Array α} :
    (l₁ ++ l₂).mapM f = (return (← l₁.mapM f) ++ (← l₂.mapM f)) := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simp

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

theorem foldlM_map [Monad m] (f : β₁ → β₂) (g : α → β₂ → m α) (l : Array β₁) (init : α) (w : stop = l.size) :
    (l.map f).foldlM g init 0 stop = l.foldlM (fun x y => g x (f y)) init 0 stop := by
  subst w
  cases l
  simp [List.foldlM_map]

theorem foldrM_map [Monad m] [LawfulMonad m] (f : β₁ → β₂) (g : β₂ → α → m α) (l : Array β₁)
    (init : α) (w : start = l.size) :
    (l.map f).foldrM g init start 0 = l.foldrM (fun x y => g (f x) y) init start 0 := by
  subst w
  cases l
  simp [List.foldrM_map]

theorem foldlM_filterMap [Monad m] [LawfulMonad m] (f : α → Option β) (g : γ → β → m γ)
    (l : Array α) (init : γ) (w : stop = (l.filterMap f).size) :
    (l.filterMap f).foldlM g init 0 stop =
      l.foldlM (fun x y => match f y with | some b => g x b | none => pure x) init := by
  subst w
  cases l
  simp [List.foldlM_filterMap]
  rfl

theorem foldrM_filterMap [Monad m] [LawfulMonad m] (f : α → Option β) (g : β → γ → m γ)
    (l : Array α) (init : γ) (w : start = (l.filterMap f).size) :
    (l.filterMap f).foldrM g init start 0 =
      l.foldrM (fun x y => match f x with | some b => g b y | none => pure y) init := by
  subst w
  cases l
  simp [List.foldrM_filterMap]
  rfl

theorem foldlM_filter [Monad m] [LawfulMonad m] (p : α → Bool) (g : β → α → m β)
    (l : Array α) (init : β) (w : stop = (l.filter p).size) :
    (l.filter p).foldlM g init 0 stop =
      l.foldlM (fun x y => if p y then g x y else pure x) init := by
  subst w
  cases l
  simp [List.foldlM_filter]

theorem foldrM_filter [Monad m] [LawfulMonad m] (p : α → Bool) (g : α → β → m β)
    (l : Array α) (init : β) (w : start = (l.filter p).size) :
    (l.filter p).foldrM g init start 0 =
      l.foldrM (fun x y => if p x then g x y else pure y) init := by
  subst w
  cases l
  simp [List.foldrM_filter]

@[simp] theorem foldlM_attachWith [Monad m]
    (l : Array α) {q : α → Prop} (H : ∀ a, a ∈ l → q a) {f : β → { x // q x} → m β} {b} (w : stop = l.size):
    (l.attachWith q H).foldlM f b 0 stop =
      l.attach.foldlM (fun b ⟨a, h⟩ => f b ⟨a, H _ h⟩) b := by
  subst w
  rcases l with ⟨l⟩
  simp [List.foldlM_map]

@[simp] theorem foldrM_attachWith [Monad m] [LawfulMonad m]
    (l : Array α) {q : α → Prop} (H : ∀ a, a ∈ l → q a) {f : { x // q x} → β → m β} {b} (w : start = l.size):
    (l.attachWith q H).foldrM f b start 0 =
      l.attach.foldrM (fun a acc => f ⟨a.1, H _ a.2⟩ acc) b := by
  subst w
  rcases l with ⟨l⟩
  simp [List.foldrM_map]

/-! ### forM -/

@[congr] theorem forM_congr [Monad m] {as bs : Array α} (w : as = bs)
    {f : α → m PUnit} :
    forM as f = forM bs f := by
  cases as <;> cases bs
  simp_all

@[simp] theorem forM_append [Monad m] [LawfulMonad m] (l₁ l₂ : Array α) (f : α → m PUnit) :
    forM (l₁ ++ l₂) f = (do forM l₁ f; forM l₂ f) := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simp

@[simp] theorem forM_map [Monad m] [LawfulMonad m] (l : Array α) (g : α → β) (f : β → m PUnit) :
    forM (l.map g) f = forM l (fun a => f (g a)) := by
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
  simp [List.forIn'_eq_foldlM, List.foldlM_map]
  congr

/-- We can express a for loop over an array which always yields as a fold. -/
@[simp] theorem forIn'_yield_eq_foldlM [Monad m] [LawfulMonad m]
    (l : Array α) (f : (a : α) → a ∈ l → β → m γ) (g : (a : α) → a ∈ l → β → γ → β) (init : β) :
    forIn' l init (fun a m b => (fun c => .yield (g a m b c)) <$> f a m b) =
      l.attach.foldlM (fun b ⟨a, m⟩ => g a m b <$> f a m b) init := by
  cases l
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

/-! ### Recognizing higher order functions using a function that only depends on the value. -/

/--
This lemma identifies monadic folds over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldlM_subtype [Monad m] {p : α → Prop} {l : Array { x // p x }}
    {f : β → { x // p x } → m β} {g : β → α → m β} {x : β}
    (hf : ∀ b x h, f b ⟨x, h⟩ = g b x) (w : stop = l.size) :
    l.foldlM f x 0 stop = l.unattach.foldlM g x 0 stop := by
  subst w
  rcases l with ⟨l⟩
  simp
  rw [List.foldlM_subtype hf]

/--
This lemma identifies monadic folds over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldrM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → β → m β} {g : α → β → m β} {x : β}
    (hf : ∀ x h b, f ⟨x, h⟩ b = g x b) (w : start = l.size) :
    l.foldrM f x start 0 = l.unattach.foldrM g x start 0:= by
  subst w
  rcases l with ⟨l⟩
  simp
  rw [List.foldrM_subtype hf]

/--
This lemma identifies monadic maps over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem mapM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → m β} {g : α → m β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.mapM f = l.unattach.mapM g := by
  rcases l with ⟨l⟩
  simp
  rw [List.mapM_subtype hf]

-- Without `filterMapM_toArray` relating `filterMapM` on `List` and `Array` we can't prove this yet:
-- @[simp] theorem filterMapM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {l : Array { x // p x }}
--     {f : { x // p x } → m (Option β)} {g : α → m (Option β)} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
--     l.filterMapM f = l.unattach.filterMapM g := by
--   rcases l with ⟨l⟩
--   simp
--   rw [List.filterMapM_subtype hf]

-- Without `flatMapM_toArray` relating `flatMapM` on `List` and `Array` we can't prove this yet:
-- @[simp] theorem flatMapM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {l : Array { x // p x }}
--     {f : { x // p x } → m (Array β)} {g : α → m (Array β)} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
--     (l.flatMapM f) = l.unattach.flatMapM g := by
--   rcases l with ⟨l⟩
--   simp
--   rw [List.flatMapM_subtype hf]

end Array
