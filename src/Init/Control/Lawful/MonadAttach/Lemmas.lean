/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Control.MonadAttach
public import Init.Control.Lawful.Lemmas

public theorem LawfulMonadAttach.canReturn_map_imp' [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m]
    {x : m α} {f : α → β} :
    MonadAttach.CanReturn (f <$> x) b → Exists fun a => f a = b ∧ MonadAttach.CanReturn x a := by
  intro h
  have h' : f <$> x = Subtype.val <$> (fun a => (⟨f a.1, _, rfl, a.2⟩ : Subtype (fun b => Exists fun a => f a = b ∧ MonadAttach.CanReturn x a))) <$> MonadAttach.attach x := by
    rw (occs := [1]) [← LawfulMonadAttach.map_attach (x := x)]
    simp [Functor.map_map]
  rw [h'] at h
  have := LawfulMonadAttach.canReturn_map_imp h
  exact this
