/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Init.Internal.Order.Basic
import all Init.System.ST

local instance [Lean.Order.CCPO α] : Nonempty α := ⟨Lean.Order.bot⟩

public section

@[specialize]
partial def Lean.Repeat.opaqueLoop {α : Sort u} [Lean.Order.CCPO α] (f : α → α) : α :=
  f (opaqueLoop f)

open Classical in
/--
Extrinsic fixpoint function used to elaborate `repeat`.
-/
@[implemented_by opaqueLoop]
def Lean.Repeat.loop {α : Sort u} [Lean.Order.CCPO α] (f : α → α) : α :=
  if h : Order.monotone f then
    Order.fix f h
  else
    opaqueLoop f

theorem Lean.Repeat.loop_eq {α : Sort u} [Lean.Order.CCPO α] {f : α → α} (h : Order.monotone f) :
    loop f = f (loop f) := by
  rw [loop, dif_pos h, ← Order.fix_eq h]

theorem Lean.Repeat.loop_induct {α : Sort u} [Lean.Order.CCPO α] {f : α → α}
    (hf : Order.monotone f) (motive : α → Prop) (hadm : Order.admissible motive)
    (h : ∀ (x : α), motive x → motive (f x)) :
    motive (loop f) := by
  rw [loop, dif_pos hf]
  exact Order.fix_induct hf motive hadm h

open Lean Order
class MonadRepeat (m : Type u → Type v) where
  toCCPO α : Nonempty (m α) → CCPO (m α)

@[expose]
def Lean.Order.NonemptyMonad (m : Type u → Type v) (α : Type u) (_h : Nonempty (m α)) : Type v :=
  m α

instance [MonadRepeat m] : CCPO (NonemptyMonad m α h) := MonadRepeat.toCCPO α h

class LawfulMonadRepeat (m : Type u → Type v) [Bind m] [MonadRepeat m] where
  bind_mono_right : ∀ {a : m α} {f₁ f₂ : α → m β}, letI := MonadRepeat.toCCPO β ⟨a >>= f₁⟩;
    (h : ∀ x, f₁ x ⊑ f₂ x) → a >>= f₁ ⊑ a >>= f₂

@[implicit_reducible]
def MonadRepeat.defaultInstance : MonadRepeat m where
  toCCPO _ _ := inferInstanceAs (CCPO (FlatOrder Classical.ofNonempty))

instance : MonadRepeat Id := .defaultInstance

instance : LawfulMonadRepeat Id where
  bind_mono_right {_ _ a _ _} h := h a.run

instance [MonadRepeat m] : MonadRepeat (ReaderT ρ m) where
  toCCPO α h :=
    haveI (s : ρ) : Nonempty (m α) := by
      rcases h with ⟨f⟩
      exact ⟨f s⟩
    inferInstanceAs (CCPO ((s : ρ) → NonemptyMonad m α (this s)))

instance [Monad m] [MonadRepeat m] [LawfulMonadRepeat m] :
    LawfulMonadRepeat (ReaderT ρ m) where
  bind_mono_right h := fun s => LawfulMonadRepeat.bind_mono_right (fun x => h x s)

instance [MonadRepeat m] : MonadRepeat (StateRefT' ω σ m) :=
  inferInstanceAs (MonadRepeat (ReaderT _ m))

instance [Monad m] [MonadRepeat m] [LawfulMonadRepeat m] :
    LawfulMonadRepeat (StateRefT' ω σ m) :=
  inferInstanceAs (LawfulMonadRepeat (ReaderT _ _))

instance : MonadRepeat Option where
  toCCPO _ _ := inferInstance

instance : LawfulMonadRepeat Option where
  bind_mono_right {α β a f₁ f₂} h := by
    rcases a with _ | x
    · exact .refl
    · apply h

open Classical in
instance : MonadRepeat (Except ε) where
  toCCPO α _ :=
    letI val : Except ε α :=
      -- if possible, don't make `.ok _` the divergence value
      if _ : Nonempty ε then .error Classical.ofNonempty
      else Classical.ofNonempty
    inferInstanceAs (CCPO (FlatOrder val))

instance : LawfulMonadRepeat (Except ε) where
  bind_mono_right {α β a f₁ f₂} h := by
    rcases a with e | x
    · exact .refl
    · apply h

instance [MonadRepeat m] : MonadRepeat (StateT σ m) where
  toCCPO α h :=
    haveI (s : σ) : Nonempty (m (α × σ)) := by
      rcases h with ⟨f⟩
      exact ⟨f s⟩
    inferInstanceAs (CCPO ((s : σ) → NonemptyMonad m (α × σ) (this s)))

instance [Monad m] [MonadRepeat m] [LawfulMonadRepeat m] :
    LawfulMonadRepeat (StateT ρ m) where
  bind_mono_right h := fun _ => LawfulMonadRepeat.bind_mono_right (fun x => h x.1 x.2)

instance [MonadRepeat m] : MonadRepeat (ExceptT ε m) where
  toCCPO α h := inferInstanceAs (CCPO (NonemptyMonad m (Except ε α) h))

instance [Monad m] [MonadRepeat m] [LawfulMonadRepeat m] :
    LawfulMonadRepeat (ExceptT ε m) where
  bind_mono_right h := by
    apply LawfulMonadRepeat.bind_mono_right (m := m)
    intro x
    cases x
    · apply @PartialOrder.rel_refl _ (_)
    · apply h

instance [MonadRepeat m] : MonadRepeat (OptionT m) where
  toCCPO α h := inferInstanceAs (CCPO (NonemptyMonad m (Option α) h))

instance [Monad m] [MonadRepeat m] [LawfulMonadRepeat m] : LawfulMonadRepeat (OptionT m) where
  bind_mono_right h := by
    apply LawfulMonadRepeat.bind_mono_right (m := m)
    intro x
    cases x
    · apply @PartialOrder.rel_refl _ (_)
    · apply h

open Classical in
instance : MonadRepeat (EStateM ε σ) where
  toCCPO α h :=
    letI val (s : σ) : EStateM.Result ε σ α :=
      -- if possible, don't make `.ok _` the divergence value
      if _ : Nonempty ε then .error Classical.ofNonempty (Classical.choice ⟨s⟩)
      else Classical.choice <| by
        rcases h with ⟨f⟩
        exact ⟨f s⟩
    inferInstanceAs (CCPO ((s : σ) → FlatOrder (val s)))

instance : LawfulMonadRepeat (EStateM ε σ) where
  bind_mono_right {α β a f₁ f₂} h := by
    intro s
    change FlatOrder.rel (EStateM.bind a f₁ s) (EStateM.bind a f₂ s)
    unfold EStateM.bind
    split
    · apply h
    · exact .refl

open Classical in
instance : MonadRepeat (EST ε σ) where
  toCCPO α h :=
    letI val (s : Void σ) : EST.Out ε σ α :=
      -- if possible, don't make `.ok _` the divergence value
      if _ : Nonempty ε then .error Classical.ofNonempty (Classical.choice ⟨s⟩)
      else Classical.choice <| by
        rcases h with ⟨f⟩
        exact ⟨f s⟩
    inferInstanceAs (CCPO ((s : Void σ) → FlatOrder (val s)))

instance : LawfulMonadRepeat (EST ε σ) where
  bind_mono_right {α β a f₁ f₂} h := by
    intro s
    change FlatOrder.rel (EST.bind a f₁ s) (EST.bind a f₂ s)
    unfold EST.bind
    split
    · apply h
    · exact .refl

open Classical in
instance : MonadRepeat (ST σ) where
  toCCPO α h :=
    haveI (s : Void σ) : Nonempty (ST.Out σ α) := by
      obtain ⟨f⟩ := h
      exact ⟨f s⟩
    inferInstanceAs (CCPO ((s : Void σ) → FlatOrder (Classical.choice (this s))))

instance : LawfulMonadRepeat (ST σ) where
  bind_mono_right {_ _ a _ _} h := fun s => h (a s).1 (a s).2

instance : MonadRepeat (EIO ε) := inferInstanceAs (MonadRepeat (EST ε _))
instance : MonadRepeat BaseIO := inferInstanceAs (MonadRepeat (ST _))

-- these don't have lawful MonadRepeat instances
instance {σ : Type u} [MonadRepeat m] : MonadRepeat (StateCpsT σ m) := .defaultInstance
instance {ε : Type u} [MonadRepeat m] : MonadRepeat (ExceptCpsT ε m) := .defaultInstance
