/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.Internal.Ensures.Def
public import Init.Control.Lawful.MonadAttach.Lemmas
import Init.RCases

set_option linter.missingDocs true

namespace Std.Do.Internal

/-- An `ErasesTo`-witnessed refinement `x` of `y` recovers `y` by projecting out the property. -/
public theorem ErasesTo.map_eq {α : Type u} {m : Type u → Type v} {P : α → Prop}
    {x : m {b : α // P b}} {y : m α} [Monad m] [LawfulMonad m] (h : ErasesTo x y) :
    Subtype.val <$> x = y := by
  simpa using h.bind_eq pure

/-- `MonadAttach.attach` is bind-faithful with `x`. -/
public theorem ErasesTo.of_attach [Monad m] [LawfulMonad m]
    [MonadAttach m] [WeaklyLawfulMonadAttach m] {α} {x : m α} :
    ErasesTo (MonadAttach.attach x) x := by
  refine ⟨fun {β} k =>?_⟩
  rw [← bind_map_left, WeaklyLawfulMonadAttach.map_attach]

/-- `pure a` is `Ensures`-witnessed at the singleton predicate `(· = a)`. -/
public theorem Ensures.pure [Monad m] [LawfulMonad m] {α : Type u} (a : α) :
    Ensures (· = a) (Pure.pure a : m α) :=
  ⟨⟨Pure.pure ⟨a, rfl⟩, ⟨fun {β} _ => by simp⟩⟩⟩

/-- Weaken an `Ensures`-witness via predicate implication. -/
public theorem Ensures.weaken {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α : Type u} {P Q : α → Prop} {x : m α}
    (h : Ensures P x) (hPQ : ∀ a, P a → Q a) : Ensures Q x := by
  obtain ⟨y, hy⟩ := h.exists_refinement
  refine ⟨⟨y >>= fun ⟨a, hp⟩ => Pure.pure ⟨a, hPQ a hp⟩, ⟨fun {β} k => ?_⟩⟩⟩
  rw [bind_assoc]; simp only [pure_bind]
  exact hy.bind_eq k

/-- Compose `Ensures`-witnesses across a monadic bind. -/
public theorem Ensures.bind {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α β : Type u} {x : m α} {P : α → Prop} {k : α → m β} {Q : β → Prop}
    (h : Ensures P x) (hk : ∀ a, P a → Ensures Q (k a)) :
    Ensures Q (x >>= k) := by
  obtain ⟨y, hy⟩ := h.exists_refinement
  obtain ⟨W, hW⟩ := Classical.skolem.mp
    (fun (a : {a : α // P a}) => (hk a.val a.property).exists_refinement)
  refine ⟨⟨y >>= fun a => W a, ⟨fun {γ} g => ?_⟩⟩⟩
  rw [bind_assoc, bind_assoc]
  refine Eq.trans ?_ (hy.bind_eq (fun a => k a >>= g))
  exact bind_congr fun a => (hW a).bind_eq g

/-- Every value returned by `x` satisfies `MonadAttach.CanReturn x`. -/
public theorem Ensures.canReturn [Monad m] [LawfulMonad m]
    [MonadAttach m] [WeaklyLawfulMonadAttach m] {α} {x : m α} :
    Ensures (MonadAttach.CanReturn x) x :=
  ⟨⟨MonadAttach.attach x, ErasesTo.of_attach⟩⟩

/-- `MonadAttach.CanReturn` implies `MayReturn` for `LawfulMonadAttach` instances. -/
public theorem MayReturn.of_canReturn [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] {x : m α} {a : α}
    (h : MonadAttach.CanReturn x a) : MayReturn x a := by
  refine ⟨fun hEns => ?_⟩
  obtain ⟨y, hy⟩ := hEns.exists_refinement
  rw [← hy.map_eq] at h
  exact LawfulMonadAttach.canReturn_map_imp h

/-- `MayReturn` implies `MonadAttach.CanReturn` for `WeaklyLawfulMonadAttach` instances. -/
public theorem MayReturn.canReturn [Monad m] [LawfulMonad m]
    [MonadAttach m] [WeaklyLawfulMonadAttach m] {x : m α} {a : α}
    (h : MayReturn x a) : MonadAttach.CanReturn x a :=
  h.imp ⟨⟨MonadAttach.attach x, ErasesTo.of_attach⟩⟩

/-- `MayReturn` is equivalent to `MonadAttach.CanReturn` for `LawfulMonadAttach` instances. -/
public theorem MayReturn.canReturn_iff [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] (x : m α) (a : α)
    : MonadAttach.CanReturn x a ↔ MayReturn x a :=
  ⟨MayReturn.of_canReturn, MayReturn.canReturn⟩

public theorem MayReturn.canReturn_eq [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] (x : m α)
    : MonadAttach.CanReturn x = MayReturn x :=
  funext fun a => propext (MayReturn.canReturn_iff (x := x) (a := a))

/-- `MonadAttach.attach`, retagged with `MayReturn` proofs, witnesses `IsAttach`. -/
public theorem IsAttach.of_attach [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] :
    IsAttach (m := m)
      (fun {_} (x : m _) =>
        MonadAttach.attach x >>= fun ⟨a, h⟩ => pure ⟨a, MayReturn.of_canReturn h⟩) := by
  refine ⟨fun {α} x => ⟨fun {β} k => ?_⟩⟩
  rw [bind_assoc]
  simp only [pure_bind]
  exact ErasesTo.of_attach.bind_eq k

end Std.Do.Internal
