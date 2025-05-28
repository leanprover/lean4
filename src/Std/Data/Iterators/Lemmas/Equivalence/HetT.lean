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

variable {α : Type v} {m : Type w → Type w'}

def CodensityT (m : Type w → Type w') (β : Type u) := ∀ α, (β → m α) → m α

@[always_inline, inline]
def CodensityT.run (f : α → m β) (x : CodensityT m α) := x _ f

@[always_inline, inline]
def CodensityT.map {β : Type u} {γ : Type u'} (f : β → γ) (x : CodensityT m β) : CodensityT m γ :=
  fun _ h => x _ (h ∘ f)

theorem CodensityT.run_map {f : α → β} {g : β → m γ} {x : CodensityT m α} :
    (x.map f).run g = x.run (g ∘ f) :=
  rfl

@[always_inline, inline]
def CodensityT.pure {α : Type w} (x : α) : CodensityT m α :=
  fun _ h => h x

theorem CodensityT.map_id {β : Type u} {x : CodensityT m β} :
    x.map id = x := rfl

theorem CodensityT.map_id' {β : Type u} {x : CodensityT m β} :
    x.map (·) = x := rfl

@[always_inline, inline]
def CodensityT.bind {β : Type u} {γ : Type u'} (x : CodensityT m β) (f : β → CodensityT m γ) : CodensityT m γ :=
  fun _ h => x _ (f · _ h)

theorem CodensityT.bind_assoc {β : Type u} {γ : Type u'} {δ : Type u''} {x : CodensityT m β}
    {f : β → CodensityT m γ} {g : γ → CodensityT m δ} :
    (x.bind f).bind g = x.bind (f · |>.bind g) := rfl

@[always_inline, inline]
def CodensityT.eval [Bind m] {α : Type w} (x : m α) : CodensityT m α :=
  fun _ h => x >>= h

instance : Monad (CodensityT m) where
  pure := CodensityT.pure
  bind := CodensityT.bind

-- protected theorem CodensityT.map_eq_mapH {β : Type u} {γ : Type u} (f : β → γ) (x : CodensityT m β) :
--     f <$> x = x.mapH f :=
--   rfl

-- protected theorem CodensityT.mapH_eq_bindH {β : Type u} {γ : Type u'} (f : β → γ) (x : CodensityT m β) :
--     x.mapH f = x.bindH (pure <| f ·) := rfl

-- @[simp]
-- protected theorem CodensityT.mapH_pure {β : Type u} {γ : Type u'} (f : β → γ) (x : β) :
--     (pure x : CodensityT m β).mapH f = pure (f x) :=
--   rfl

-- @[simp]
-- protected theorem CodensityT.bindH_pure {β : Type u} {γ : Type u'} (f : β → CodensityT m γ) (x : β) :
--     (pure x : CodensityT m β).bindH f = f x :=
--   rfl

-- protected theorem CodensityT.mapH_bindH {β : Type u} {γ : Type u'} {x : CodensityT m β} {f : β → CodensityT m γ}
--     {δ : Type u''} {g : γ → δ} :
--     (x.bindH f |>.mapH g) = x.bindH (f · |>.mapH g) :=
--   rfl

-- protected theorem CodensityT.map_bindH {β : Type u} {γ : Type u'} {x : CodensityT m β} {f : β → CodensityT m γ}
--     {δ : Type u'} {g : γ → δ} :
--     g <$> (x.bindH f) = x.bindH (g <$> f ·) :=
--   rfl

protected theorem CodensityT.map_map {β : Type u} {γ : Type u'} {x : CodensityT m β} {f : β → γ}
    {δ : Type u''} {g : γ → δ} :
    (x.map f |>.map g) = x.map (g ∘ f) :=
  rfl


theorem CodensityT.comp_map (f : α → β) (g : β → γ) :
    CodensityT.map (m := m) (g ∘ f) = CodensityT.map (m := m) g ∘ CodensityT.map (m := m) f := by
  rfl

def CodensityT.lift [Monad m] {α : Type w} (x : m α) : CodensityT m α :=
  fun _ h => x >>= h

theorem CodensityT.run_lift [Monad m] {α : Type w} {f : α → m β} {x : m α} :
    (CodensityT.lift x).run f = x >>= f :=
  rfl

theorem CodensityT.lift_map [Monad m] [LawfulMonad m] {α : Type w} {x : m α} {f : α → β} :
    (CodensityT.lift (f <$> x)) = (CodensityT.lift x).map f := by
  unfold CodensityT
  ext α h
  simp [lift, map]; rfl

instance [Monad m] : MonadLift m (CodensityT m) where
  monadLift x _ f := x >>= f

end Std.Iterators
