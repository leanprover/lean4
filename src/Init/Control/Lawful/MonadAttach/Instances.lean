/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Control.Reader
public import Init.Control.Lawful.Instances
import Init.Control.Lawful.MonadAttach.Lemmas

public instance [Monad m] [LawfulMonad m] [MonadAttach m] [WeaklyLawfulMonadAttach m] :
    WeaklyLawfulMonadAttach (ReaderT ρ m) where
  map_attach := by
    simp only [Functor.map, MonadAttach.attach, Functor.map_map, WeaklyLawfulMonadAttach.map_attach]
    intros; rfl

public instance [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] :
    LawfulMonadAttach (ReaderT ρ m) where
  canReturn_map_imp := by
    simp only [Functor.map, MonadAttach.CanReturn, ReaderT.run]
    rintro _ _ x a ⟨r, h⟩
    apply LawfulMonadAttach.canReturn_map_imp h

public instance [Monad m] [LawfulMonad m] [MonadAttach m] [WeaklyLawfulMonadAttach m] :
    WeaklyLawfulMonadAttach (StateT σ m) where
  map_attach := by
    intro α x
    simp only [Functor.map, StateT, funext_iff, StateT.map, bind_pure_comp, MonadAttach.attach,
      Functor.map_map]
    exact fun s => WeaklyLawfulMonadAttach.map_attach

public instance [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] :
    LawfulMonadAttach (StateT σ m) where
  canReturn_map_imp := by
    simp only [Functor.map, MonadAttach.CanReturn, StateT.run, StateT.map, bind_pure_comp]
    rintro _ _ x a ⟨s, s', h⟩
    obtain ⟨a, h, h'⟩ := LawfulMonadAttach.canReturn_map_imp' h
    cases h'
    exact a.1.2

public instance [Monad m] [LawfulMonad m] [MonadAttach m] [WeaklyLawfulMonadAttach m] :
    WeaklyLawfulMonadAttach (ExceptT ε m) where
  map_attach {α} x := by
    simp only [Functor.map, MonadAttach.attach, ExceptT.map]
    simp
    conv => rhs; rw [← WeaklyLawfulMonadAttach.map_attach (m := m) (x := x)]
    simp only [map_eq_pure_bind]
    apply bind_congr; intro a
    match a with
    | ⟨.ok _, _⟩ => simp
    | ⟨.error _, _⟩ => simp

public instance [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] :
    LawfulMonadAttach (ExceptT ε m) where
  canReturn_map_imp {α P x a} := by
    simp only [Functor.map, MonadAttach.CanReturn, ExceptT.map, ExceptT.mk]
    let x' := (fun a => show Subtype (fun a : Except _ _ => match a with | .ok a => P a | .error e => True) from ⟨match a with | .ok a => .ok a.1 | .error e => .error e, by cases a <;> simp [Subtype.property]⟩) <$> show m _ from x
    have := LawfulMonadAttach.canReturn_map_imp (m := m) (x := x') (a := .ok a)
    simp only at this
    intro h
    apply this
    simp only [x', map_eq_pure_bind, bind_assoc]
    refine cast ?_ h
    congr 1
    apply bind_congr; intro a
    split <;> simp

public instance [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m] :
    WeaklyLawfulMonadAttach (StateRefT' ω σ m) :=
  inferInstanceAs (WeaklyLawfulMonadAttach (ReaderT _ _))

public instance [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m] :
    LawfulMonadAttach (StateRefT' ω σ m) :=
  inferInstanceAs (LawfulMonadAttach (ReaderT _ _))

section

attribute [local instance] MonadAttach.trivial

public instance [Monad m] [LawfulMonad m] :
    WeaklyLawfulMonadAttach m where
  map_attach := by simp [MonadAttach.attach]

end
