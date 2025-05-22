/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import all Init.Data.Vector.Basic
import Init.Data.Vector.Lemmas
import Init.Data.Vector.Attach
import Init.Data.Array.Monadic
import Init.Control.Lawful.Lemmas

/-!
# Lemmas about `Vector.forIn'` and `Vector.forIn`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

open Nat

/-! ## Monadic operations -/

@[simp] theorem map_toArray_inj [Monad m] [LawfulMonad m]
    {xs : m (Vector α n)} {ys : m (Vector α n)} :
   toArray <$> xs = toArray <$> ys ↔ xs = ys :=
  _root_.map_inj_right (by simp)

/-! ### mapM -/

@[simp]
theorem mapM_pure [Monad m] [LawfulMonad m] {xs : Vector α n} (f : α → β) :
    xs.mapM (m := m) (pure <| f ·) = pure (xs.map f) := by
  apply map_toArray_inj.mp
  simp

@[simp] theorem mapM_map [Monad m] [LawfulMonad m] {f : α → β} {g : β → m γ} {xs : Vector α n} :
    (xs.map f).mapM g = xs.mapM (g ∘ f) := by
  apply map_toArray_inj.mp
  simp

@[congr] theorem mapM_congr [Monad m] {xs ys : Vector α n} (w : xs = ys)
    {f : α → m β} :
    xs.mapM f = ys.mapM f := by
  subst w
  simp

@[simp] theorem mapM_mk_empty [Monad m] {f : α → m β} :
    (mk #[] rfl).mapM f = pure #v[] := by
  unfold mapM
  unfold mapM.go
  simp

@[simp] theorem mapM_append [Monad m] [LawfulMonad m]
    {f : α → m β} {xs : Vector α n} {ys : Vector α n'} :
    (xs ++ ys).mapM f = (return (← xs.mapM f) ++ (← ys.mapM f)) := by
  apply map_toArray_inj.mp
  suffices toArray <$> (xs ++ ys).mapM f = (return (← toArray <$> xs.mapM f) ++ (← toArray <$> ys.mapM f)) by
    rw [this]
    simp only [bind_pure_comp, Functor.map_map, bind_map_left, map_bind, toArray_append]
  simp

/-! ### foldlM and foldrM -/

theorem foldlM_map [Monad m] {f : β₁ → β₂} {g : α → β₂ → m α} {xs : Vector β₁ n} {init : α} :
    (xs.map f).foldlM g init = xs.foldlM (fun x y => g x (f y)) init := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldlM_map]

theorem foldrM_map [Monad m] [LawfulMonad m] {f : β₁ → β₂} {g : β₂ → α → m α} {xs : Vector β₁ n} {init : α} :
    (xs.map f).foldrM g init = xs.foldrM (fun x y => g (f x) y) init := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldrM_map]

@[simp] theorem foldlM_attachWith [Monad m]
    {xs : Vector α n} {q : α → Prop} (H : ∀ a, a ∈ xs → q a) {f : β → { x // q x} → m β} {b} :
    (xs.attachWith q H).foldlM f b = xs.attach.foldlM (fun b ⟨a, h⟩ => f b ⟨a, H _ h⟩) b := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldlM_map]

@[simp] theorem foldrM_attachWith [Monad m] [LawfulMonad m]
    {xs : Vector α n} {q : α → Prop} (H : ∀ a, a ∈ xs → q a) {f : { x // q x} → β → m β} {b} :
    (xs.attachWith q H).foldrM f b = xs.attach.foldrM (fun a acc => f ⟨a.1, H _ a.2⟩ acc) b := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldrM_map]

/-! ### forM -/

@[congr] theorem forM_congr [Monad m] {as bs : Vector α n} (w : as = bs)
    {f : α → m PUnit} :
    forM as f = forM bs f := by
  cases as <;> cases bs
  simp_all

@[simp] theorem forM_append [Monad m] [LawfulMonad m] {xs : Vector α n} {ys : Vector α n'} {f : α → m PUnit} :
    forM (xs ++ ys) f = (do forM xs f; forM ys f) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp

@[simp] theorem forM_map [Monad m] [LawfulMonad m] {xs : Vector α n} {g : α → β} {f : β → m PUnit} :
    forM (xs.map g) f = forM xs (fun a => f (g a)) := by
  rcases xs with ⟨xs, rfl⟩
  simp

/-! ### forIn' -/

@[congr] theorem forIn'_congr [Monad m] {xs ys : Vector α n} (w : xs = ys)
    {b b' : β} (hb : b = b')
    {f : (a' : α) → a' ∈ xs → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ ys → β → m (ForInStep β)}
    (h : ∀ a m b, f a (by simpa [w] using m) b = g a m b) :
    forIn' xs b f = forIn' ys b' g := by
  cases xs <;> cases ys
  simp only [eq_mk, mem_mk, forIn'_mk] at w h ⊢
  exact Array.forIn'_congr w hb h

/--
We can express a for loop over a vector as a fold,
in which whenever we reach `.done b` we keep that value through the rest of the fold.
-/
theorem forIn'_eq_foldlM [Monad m] [LawfulMonad m]
    {xs : Vector α n} (f : (a : α) → a ∈ xs → β → m (ForInStep β)) (init : β) :
    forIn' xs init f = ForInStep.value <$>
      xs.attach.foldlM (fun b ⟨a, m⟩ => match b with
        | .yield b => f a m b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.forIn'_eq_foldlM]
  rfl

/-- We can express a for loop over a vector which always yields as a fold. -/
@[simp] theorem forIn'_yield_eq_foldlM [Monad m] [LawfulMonad m]
    {xs : Vector α n} (f : (a : α) → a ∈ xs → β → m γ) (g : (a : α) → a ∈ xs → β → γ → β) (init : β) :
    forIn' xs init (fun a m b => (fun c => .yield (g a m b c)) <$> f a m b) =
      xs.attach.foldlM (fun b ⟨a, m⟩ => g a m b <$> f a m b) init := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem forIn'_pure_yield_eq_foldl [Monad m] [LawfulMonad m]
    {xs : Vector α n} (f : (a : α) → a ∈ xs → β → β) (init : β) :
    forIn' xs init (fun a m b => pure (.yield (f a m b))) =
      pure (f := m) (xs.attach.foldl (fun b ⟨a, h⟩ => f a h b) init) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.forIn'_pure_yield_eq_foldl, Array.foldl_map]

@[simp] theorem idRun_forIn'_yield_eq_foldl
    {xs : Vector α n} (f : (a : α) → a ∈ xs → β → Id β) (init : β) :
    (forIn' xs init (fun a m b => .yield <$> f a m b)).run =
      xs.attach.foldl (fun b ⟨a, h⟩ => f a h b |>.run) init :=
  forIn'_pure_yield_eq_foldl _ _

@[deprecated forIn'_yield_eq_foldl (since := "2025-05-21")]
theorem forIn'_yield_eq_foldl
    {xs : Vector α n} (f : (a : α) → a ∈ xs → β → β) (init : β) :
    forIn' (m := Id) xs init (fun a m b => .yield (f a m b)) =
      xs.attach.foldl (fun b ⟨a, h⟩ => f a h b) init :=
  forIn'_pure_yield_eq_foldl _ _

@[simp] theorem forIn'_map [Monad m] [LawfulMonad m]
    {xs : Vector α n} (g : α → β) (f : (b : β) → b ∈ xs.map g → γ → m (ForInStep γ)) :
    forIn' (xs.map g) init f = forIn' xs init fun a h y => f (g a) (mem_map_of_mem h) y := by
  rcases xs with ⟨xs, rfl⟩
  simp

/--
We can express a for loop over a vector as a fold,
in which whenever we reach `.done b` we keep that value through the rest of the fold.
-/
theorem forIn_eq_foldlM [Monad m] [LawfulMonad m]
    {xs : Vector α n} (f : α → β → m (ForInStep β)) (init : β) :
    forIn xs init f = ForInStep.value <$>
      xs.foldlM (fun b a => match b with
        | .yield b => f a b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.forIn_eq_foldlM]
  rfl

/-- We can express a for loop over a vector which always yields as a fold. -/
@[simp] theorem forIn_yield_eq_foldlM [Monad m] [LawfulMonad m]
    {xs : Vector α n} (f : α → β → m γ) (g : α → β → γ → β) (init : β) :
    forIn xs init (fun a b => (fun c => .yield (g a b c)) <$> f a b) =
      xs.foldlM (fun b a => g a b <$> f a b) init := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem forIn_pure_yield_eq_foldl [Monad m] [LawfulMonad m]
    {xs : Vector α n} (f : α → β → β) (init : β) :
    forIn xs init (fun a b => pure (.yield (f a b))) =
      pure (f := m) (xs.foldl (fun b a => f a b) init) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.forIn_pure_yield_eq_foldl, Array.foldl_map]

@[simp] theorem idRun_forIn_yield_eq_foldl
    {xs : Vector α n} (f : α → β → Id β) (init : β) :
    (forIn xs init (fun a b => .yield <$> f a b)).run =
      xs.foldl (fun b a => f a b |>.run) init :=
  forIn_pure_yield_eq_foldl _ _

@[deprecated idRun_forIn_yield_eq_foldl (since := "2025-05-21")]
theorem forIn_yield_eq_foldl
    {xs : Vector α n} (f : α → β → β) (init : β) :
    forIn (m := Id) xs init (fun a b => .yield (f a b)) =
      xs.foldl (fun b a => f a b) init :=
  forIn_pure_yield_eq_foldl _ _

@[simp] theorem forIn_map [Monad m] [LawfulMonad m]
    {xs : Vector α n} (g : α → β) (f : β → γ → m (ForInStep γ)) :
    forIn (xs.map g) init f = forIn xs init fun a y => f (g a) y := by
  rcases xs with ⟨xs, rfl⟩
  simp


/-! ### allM and anyM -/

@[simp] theorem anyM_pure [Monad m] [LawfulMonad m] {p : α → Bool} {xs : Vector α n} :
    xs.anyM (m := m) (pure <| p ·) = pure (xs.any p) := by
  cases xs
  simp

@[simp] theorem allM_pure [Monad m] [LawfulMonad m] {p : α → Bool} {xs : Vector α n} :
    xs.allM (m := m) (pure <| p ·) = pure (xs.all p) := by
  cases xs
  simp

/-! ### findM? and findSomeM? -/

theorem findM?_pure {m} [Monad m] [LawfulMonad m] {p : α → Bool} {xs : Vector α n} :
    findM? (m := m) (pure <| p ·) xs = pure (xs.find? p) := by
  cases xs
  simp

@[simp]
theorem findSomeM?_pure [Monad m] [LawfulMonad m] {f : α → Option β} {xs : Vector α n} :
    findSomeM? (m := m) (pure <| f ·) xs = pure (xs.findSome? f) := by
  cases xs
  simp

end Vector
