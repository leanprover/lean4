/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Control.Lawful.Basic
import Init.Data.Subtype
import Init.PropLemmas

namespace Std.Iterators

structure HetT (m : Type w → Type w') (α : Type v) where
  Property : α → Prop
  run : {β : Type w} → (f : (a : α) → Property a → m β) → m β

instance (m : Type w → Type w') [Monad m] : MonadLift m (HetT m) where
  monadLift x := ⟨fun _ => True, fun f => x >>= fun a => f a .intro⟩

def HetT.lift {α : Type w} {m : Type w → Type w'} [Monad m] (x : m α) :
    HetT m α :=
  x

protected def HetT.pure {m : Type w → Type w'} [Pure m] {α : Type v}
    (a : α) : HetT m α :=
  ⟨fun y => a = y, fun f => f a rfl⟩

protected def HetT.map {m : Type w → Type w'} {α : Type u} {β : Type v}
    (f : α → β) (x : HetT m α) : HetT m β :=
  ⟨fun b => ∃ a : α, x.Property a ∧ f a = b, fun g => x.run fun a h => g (f a) ⟨a, h, rfl⟩⟩

protected def HetT.pmap {m : Type w → Type w'} {α : Type u} {β : Type v}
    (x : HetT m α) (f : (a : α) → x.Property a → β) : HetT m β :=
  ⟨fun b => ∃ (a : α) (h : x.Property a), f a h = b, fun g => x.run fun a h => g (f a h) ⟨a, h, rfl⟩⟩

protected def HetT.bind {m : Type w → Type w'} [Monad m] {α : Type u} {β : Type v}
    (x : HetT m α) (f : α → HetT m β) : HetT m β :=
  ⟨fun b => ∃ a, x.Property a ∧ (f a).Property b, fun g => x.run fun a h => (f a).run fun b hb => g b ⟨a, h, hb⟩⟩

-- /--
-- A version of `bind` that provides a proof of the previous postcondition to the mapping function.
-- -/
-- @[always_inline, inline]
-- protected def HetT.pbind {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type w}
--     (x : HetT m α) (f : Subtype x.Property → HetT m β) : HetT m β :=
--   ⟨fun b => ∃ a, (f a).Property b,
--     x.operation >>= fun a => (fun b => ⟨b.val, a, b.property⟩) <$> (f a).operation⟩

-- /--
-- Lifts an operation from `m` to `PostConditionT m` and then applies `HetT.map`.
-- -/
-- @[always_inline, inline]
-- protected def HetT.liftMap {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type w}
--     (f : α → β) (x : m α) : HetT m β :=
--   ⟨fun b => ∃ a, f a = b, (fun a => ⟨f a, a, rfl⟩) <$> x⟩

-- /--
-- Converts an operation from `PostConditionT m` to `m`, discarding the postcondition.
-- -/
-- @[always_inline, inline]
-- def HetT.run {m : Type w → Type w'} [Monad m] {α : Type w} (x : HetT m α) :
--     m α :=
--   (fun a => a.val) <$> x.operation

instance {m : Type w → Type w'} [Functor m] : Functor (HetT m) where
  map := HetT.map

instance {m : Type w → Type w'} [Monad m] : Monad (HetT m) where
  pure := HetT.pure
  bind := HetT.bind

@[simp]
theorem HetT.property_pure {m : Type w → Type w'} [Monad m] {α : Type w}
    {x : α} :
    (pure x : HetT m α).Property = (x = ·) :=
  rfl

-- TODO: Init.Core
theorem HEq.congrArg {α : Sort u} {β : α → Type v} (f : (a : α) → β a) {a a'} (h : a = a') :
    HEq (f a) (f a') := by
  cases h; rfl

theorem HEq.congrArg₂ {α : Sort u} {β : α → Sort v} {γ : (a : α) → (b : β a) → Sort w}
    (f : (a : α) → (b : β a) → γ a b)
    {a a' b b'} (h : a = a') (h' : HEq b b') : HEq (f a b) (f a' b') := by
  cases h; cases h'; rfl

theorem HEq.congrArg₃ {α : Sort u} {β : (a : α) → Sort v} {γ : (a : α) → (b : β a) → Sort w}
    {δ : (a : α) → (b : β a) → (c : γ a b) → Sort x}
    (f : (a : α) → (b : β a) → (c : γ a b) → δ a b c)
    {a a' b b' c c'} (h₁ : a = a') (h₂ : HEq b b') (h₃ : HEq c c') : HEq (f a b c) (f a' b' c') := by
  cases h₁; cases h₂; cases h₃; rfl

theorem HEq.congrArg₄ {α : Sort u} {β : (a : α) → Sort v} {γ : (a : α) → (b : β a) → Sort w}
    {δ : (a : α) → (b : β a) → (c : γ a b) → Sort x} {ε : (a : α) → (b : β a) → (c : γ a b) →
      (d : δ a b c) → Sort y}
    (f : (a : α) → (b : β a) → (c : γ a b) → (d : δ a b c) → ε a b c d)
    {a a' b b' c c' d d'} (h₁ : a = a') (h₂ : HEq b b') (h₃ : HEq c c') (h₄ : HEq d d') :
    HEq (f a b c d) (f a' b' c' d') := by
  cases h₁; cases h₂; cases h₃; cases h₄; rfl

theorem HetT.ext {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type v} {x y : HetT m α}
    (h : x.Property = y.Property) (h' : ∀ γ (f : (a : α) → x.Property a → m γ), x.run f = y.run (fun a ha => f a (h ▸ ha))) :
    x = y := by
  cases x; cases y; cases h
  simp only [mk.injEq, heq_eq_eq, true_and]
  simp only at h'
  funext γ f
  simp [h' γ f]

theorem HetT.ext_iff {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type v} {x y : HetT m α} :
    x = y ↔ ∃ h : x.Property = y.Property, ∀ γ (f : (a : α) → x.Property a → m γ), x.run f = y.run (fun a ha => f a (h ▸ ha)) := by
  constructor
  · rintro rfl
    exact ⟨rfl, by simp⟩
  · rintro ⟨h, h'⟩
    exact HetT.ext h h'

@[simp]
protected theorem HetT.map_eq_pure_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {f : α → β} {x : HetT m α} :
    x.map f = x.bind (pure ∘ f) := by
  apply HetT.ext <;> simp [HetT.map, HetT.bind, Pure.pure, HetT.pure]

@[simp]
protected theorem HetT.pure_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {f : α → HetT m β} {a : α} :
    (pure a : HetT m α).bind f = f a := by
  apply HetT.ext <;> simp [pure, HetT.pure, HetT.bind]

@[simp]
protected theorem HetT.bind_pure {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {x : HetT m α} :
    x.bind pure = x := by
  apply HetT.ext <;> simp [pure, HetT.pure, HetT.bind]

@[simp]
protected theorem HetT.bind_assoc {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {γ : Type x} {x : HetT m α} {f : α → HetT m β} {g : β → HetT m γ} :
    (x.bind f).bind g = x.bind (fun a => (f a).bind g) := by
  apply HetT.ext
  · simp [HetT.bind]
  · simp only [HetT.bind, bind_assoc, bind_map_left, map_bind, Functor.map_map]
    ext c
    constructor
    · rintro ⟨b, ⟨a, ha, hb⟩, h⟩
      exact ⟨a, ha, b, hb, h⟩
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨b, ⟨a, ha, hb⟩, h⟩

@[simp]
protected theorem HetT.map_pure {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {f : α → β} {a : α} :
    (pure a : HetT m α).map f = pure (f a) := by
  apply HetT.ext <;> simp [pure, Functor.map, HetT.map, HetT.pure]

@[simp]
protected theorem HetT.comp_map {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {γ : Type x} {f : α → β} {g : β → γ} {x : HetT m α} :
    x.map (g ∘ f) = (x.map f).map g := by
  simp; rfl

protected theorem HetT.pmap_map {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {γ : Type x}
    {x : HetT m α} {f : α → β} {g : (b : β) → (x.map f).Property b → γ} :
    (x.map f).pmap g = x.pmap (fun a ha => g (f a) ⟨a, ha, rfl⟩) := by
  apply ext
  · intro γ f
    simp [HetT.map, HetT.pmap]
  · simp only [HetT.pmap, HetT.map]
    ext c
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩

protected theorem HetT.map_pmap {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {γ : Type x}
    {x : HetT m α} {f : (a : α) → (ha : x.Property a) → β} {g : β → γ} :
    (x.pmap f).map g = x.pmap (fun a ha => g (f a ha)) := by
  apply ext
  · intro γ f
    simp [HetT.map, HetT.pmap]
  · simp only [HetT.pmap, HetT.map]
    ext c
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩

instance [Monad m] [LawfulMonad m] : LawfulMonad (HetT m) where
  map_const {α β} := by ext a x; simp [Functor.mapConst, Function.const_apply, Functor.map]
  id_map {α} x := by simp [Functor.map]
  comp_map {α β γ} g h := by intro x; simp [Functor.map]; rfl
  seqLeft_eq {α β} x y := by simp [SeqLeft.seqLeft, Functor.map, Seq.seq]; rfl
  seqRight_eq {α β} x y := by simp [Seq.seq, SeqRight.seqRight, Functor.map]
  pure_seq g x := by simp [Seq.seq, Functor.map]
  bind_pure_comp f x := by simp [Functor.map, Bind.bind]; rfl
  bind_map f x := by simp [Seq.seq, Functor.map]; rfl
  pure_bind x f := HetT.pure_bind
  bind_assoc x f g := HetT.bind_assoc

@[simp]
theorem HetT.property_map {m : Type w → Type w'} [Functor m] {α : Type u} {β : Type v}
    {x : HetT m α} {f : α → β} {b : β} :
    (x.map f).Property b ↔ (∃ a, f a = b ∧ x.Property a) := by
  simp only [HetT.map]
  apply Iff.intro
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, rfl, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨a, ha, rfl⟩

end Std.Iterators
