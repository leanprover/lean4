/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Control.Lawful.Basic
import Init.Data.Subtype
import Init.PropLemmas
import Init.Classical

namespace Std.Iterators

variable {α : Type v} {m : Type w → Type w'} [Monad m]

structure HetT.Raw (m : Type w → Type w') (α : Type x) where
  Squashed : Type w
  inflate : Squashed → α
  operation : m Squashed

def HetT.Raw.map (f : α → β) (x : Raw m α) : Raw m β :=
  ⟨x.Squashed, f ∘ x.inflate, x.operation⟩

theorem HetT.Raw.comp_map {m : Type w → Type w'} (f : α → β) (g : β → γ) :
    Raw.map (m := m) (g ∘ f) = Raw.map (m := m) g ∘ Raw.map (m := m) f := by
  rfl

def HetT.Raw.lift {α : Type w} {m : Type w → Type w'} (x : m α) : Raw m α :=
  ⟨α, id, x⟩

def HetT.Raw.run (f : α → β) (x : Raw m α) : m β :=
  (f ∘ x.inflate) <$> x.operation

def HetT.Rel (x y : HetT.Raw m α) : Prop :=
  ∀ (β) (f : α → β), (f ∘ x.inflate) <$> x.operation = (f ∘ y.inflate) <$> y.operation

def HetT m [Monad m] α := Quot (α := HetT.Raw m α) HetT.Rel

def HetT.pure {α : Type w} (a : α) : HetT m α :=
  Quot.mk _ ⟨α, id, Pure.pure a⟩

private theorem comp_assoc (f : α → β) (g : β → γ) (h : γ → δ) : (h ∘ g) ∘ f = h ∘ (g ∘ f) :=
  rfl

def HetT.map (f : α → β) : HetT m α → HetT m β :=
  Quot.lift (fun x => .mk _ (x.map f))
    (by
      intro x y h
      apply Quot.sound
      intro α' f
      rename_i f'
      simp only [Raw.map]
      simp only [← comp_assoc]
      exact h α' _)

theorem HetT.comp_map (f : α → β) (g : β → γ) :
    HetT.map (m := m) (g ∘ f) = HetT.map (m := m) g ∘ HetT.map (m := m) f := by
  ext x
  rcases x with ⟨x⟩
  simp [map, Raw.comp_map]

theorem HetT.map_map (f : α → β) (g : β → γ) {x} :
    HetT.map (m := m) g (HetT.map (m := m) f x) = HetT.map (m := m) (g ∘ f) x := by
  simp [HetT.comp_map]

def HetT.lift {α : Type w} (x : m α) : HetT m α :=
  .mk _ (Raw.lift x)

theorem HetT.lift_map [LawfulMonad m] {α : Type w} {x : m α} {f : α → β} :
    (HetT.lift (f <$> x)) = (HetT.lift x).map f := by
  apply Quot.sound
  intro γ f
  simp only [Raw.lift, Function.comp_id, Functor.map_map, Raw.map]
  rfl

def HetT.run (f : α → β) : HetT m α → m β :=
  Quot.lift (fun x => x.run f) (by intro x y h; apply h)

end Std.Iterators
