/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Internal.Order.Basic
import all Init.System.ST  -- for `EST.bind` in `MonadTail` instance

set_option linter.missingDocs true

public section

namespace Lean.Order

/--
A *tail monad* is a monad whose bind operation preserves a chosen ordering of the continuation.
Specifically, `MonadTail m` asserts that every `m β` carries a chain-complete partial order (CCPO)
and that `>>=` is monotone in its second (continuation) argument with respect to that order.

This is a weaker requirement than `MonoBind`, which requires monotonicity in both arguments.
`MonadTail` is sufficient for `partial_fixpoint`-like recursive definitions where the
recursive call only appears in the continuation (second argument) of `>>=`.
-/
class MonadTail (m : Type u → Type v) [Bind m] where
  /-- Every `m β` with `Nonempty β` has a chain-complete partial order. -/
  instCCPO β [Nonempty β] : CCPO (m β)
  /-- Bind is monotone in the second (continuation) argument. -/
  bind_mono_right {a : m α} {f₁ f₂ : α → m β} [Nonempty β] (h : ∀ x, f₁ x ⊑ f₂ x) :
    a >>= f₁ ⊑ a >>= f₂

attribute [implicit_reducible] MonadTail.instCCPO
attribute [instance] MonadTail.instCCPO

@[scoped partial_fixpoint_monotone]
theorem MonadTail.monotone_bind_right
    (m : Type u → Type v) [Monad m] [MonadTail m]
    {α β : Type u} [Nonempty β]
    {γ : Sort w} [PartialOrder γ]
    (f : m α) (g : γ → α → m β)
    (hmono : monotone g) :
    monotone (fun (x : γ) => f >>= g x) :=
  fun _ _ h => MonadTail.bind_mono_right (hmono _ _ h)

instance : MonadTail Id where
  instCCPO _ := inferInstanceAs (CCPO (FlatOrder (b := Classical.ofNonempty)))
  bind_mono_right h := h _

instance {σ : Type u} {m : Type u → Type v} [Monad m] [MonadTail m] [Nonempty σ] :
    MonadTail (StateT σ m) where
  instCCPO α := inferInstanceAs (CCPO (σ → m (α × σ)))
  bind_mono_right h := by
    intro s
    show StateT.bind _ _ s ⊑ StateT.bind _ _ s
    simp only [StateT.bind]
    apply MonadTail.bind_mono_right (m := m)
    intro ⟨x, s'⟩
    exact h x s'

instance {ε : Type u} {m : Type u → Type v} [Monad m] [MonadTail m] :
    MonadTail (ExceptT ε m) where
  instCCPO β := MonadTail.instCCPO (Except ε β)
  bind_mono_right h := by
    apply MonadTail.bind_mono_right (m := m)
    intro x
    cases x with
    | error => exact PartialOrder.rel_refl
    | ok a => exact h a

instance : MonadTail (Except ε) where
  instCCPO β := inferInstanceAs (CCPO (FlatOrder (b := Classical.ofNonempty)))
  bind_mono_right h := by
    cases ‹Except _ _› with
    | error => exact FlatOrder.rel.refl
    | ok a => exact h a

instance {m : Type u → Type v} [Monad m] [MonadTail m] :
    MonadTail (OptionT m) where
  instCCPO β := MonadTail.instCCPO (Option β)
  bind_mono_right h := by
    apply MonadTail.bind_mono_right (m := m)
    intro x
    cases x with
    | none => exact PartialOrder.rel_refl
    | some a => exact h a

instance : MonadTail Option where
  instCCPO _ := inferInstance
  bind_mono_right h := MonoBind.bind_mono_right h

instance {ρ : Type u} {m : Type u → Type v} [Monad m] [MonadTail m] :
    MonadTail (ReaderT ρ m) where
  instCCPO α := inferInstanceAs (CCPO (ρ → m α))
  bind_mono_right h := by
    intro r
    show ReaderT.bind _ _ r ⊑ ReaderT.bind _ _ r
    simp only [ReaderT.bind]
    apply MonadTail.bind_mono_right (m := m)
    intro x
    exact h x r

set_option linter.missingDocs false in
noncomputable def ST.bot' [Nonempty α] (s : Void σ) : @FlatOrder (ST.Out σ α) (.mk Classical.ofNonempty (Classical.choice ⟨s⟩)) :=
  .mk Classical.ofNonempty (Classical.choice ⟨s⟩)

instance [Nonempty α] : CCPO (ST σ α) where
  rel := PartialOrder.rel (α := ∀ s, FlatOrder (ST.bot' s))
  rel_refl := PartialOrder.rel_refl
  rel_antisymm := PartialOrder.rel_antisymm
  rel_trans := PartialOrder.rel_trans
  has_csup hchain := CCPO.has_csup (α := ∀ s, FlatOrder (ST.bot' s)) hchain

instance : MonadTail (ST σ) where
  instCCPO _ := inferInstance
  bind_mono_right {_ _ a f₁ f₂} _ h := by
    intro w
    change FlatOrder.rel (ST.bind a f₁ w) (ST.bind a f₂ w)
    simp only [ST.bind]
    apply h

instance : MonadTail BaseIO :=
  inferInstanceAs (MonadTail (ST IO.RealWorld))

instance [Nonempty ε] : MonadTail (EST ε σ) where
  instCCPO _ := inferInstance
  bind_mono_right h := MonoBind.bind_mono_right h

instance [Nonempty ε] : MonadTail (EIO ε) :=
  inferInstanceAs (MonadTail (EST ε IO.RealWorld))

instance : MonadTail IO :=
  inferInstanceAs (MonadTail (EIO IO.Error))

instance {ω : Type} {σ : Type} {m : Type → Type} [Monad m] [MonadTail m] :
    MonadTail (StateRefT' ω σ m) :=
  inferInstanceAs (MonadTail (ReaderT (ST.Ref ω σ) m))

end Lean.Order
