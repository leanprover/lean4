/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Control.MonadAttach
public import Init.Control.Lawful.Lemmas

public theorem LawfulMonadAttach.canReturn_bind_imp' [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m]
    {x : m α} {f : α → m β} :
    MonadAttach.CanReturn (x >>= f) b → Exists fun a => MonadAttach.CanReturn x a ∧ MonadAttach.CanReturn (f a) b := by
  intro h
  let P (b : β) := Exists fun a => MonadAttach.CanReturn x a ∧ MonadAttach.CanReturn (f a) b
  have h' : (x >>= f) = Subtype.val <$> (MonadAttach.attach x >>= (fun a => (do
      let b ← MonadAttach.attach (f a)
      return ⟨b.1, a.1, a.2, b.2⟩ : m (Subtype P)))) := by
    simp only [map_bind, map_pure]
    simp only [bind_pure_comp, LawfulMonadAttach.map_attach]
    rw (occs := [1]) [← LawfulMonadAttach.map_attach (x := x)]
    simp
  rw [h'] at h
  have := LawfulMonadAttach.canReturn_map_imp h
  exact this

public theorem LawfulMonadAttach.eq_of_canReturn_pure [Monad m] [MonadAttach m]
    [LawfulMonad m] [LawfulMonadAttach m] {a b : α}
    (h : MonadAttach.CanReturn (m := m) (pure a) b) :
    a = b := by
  let x : m (Subtype (a = ·)) := pure ⟨a, rfl⟩
  have : pure a = Subtype.val <$> x := by simp [x]
  rw [this] at h
  exact LawfulMonadAttach.canReturn_map_imp h

public theorem LawfulMonadAttach.canReturn_map_imp' [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m]
    {x : m α} {f : α → β} :
    MonadAttach.CanReturn (f <$> x) b → Exists fun a => MonadAttach.CanReturn x a ∧ f a = b := by
  rw [map_eq_pure_bind]
  intro h
  obtain ⟨a, h, h'⟩ := canReturn_bind_imp' h
  exact ⟨a, h, eq_of_canReturn_pure h'⟩
