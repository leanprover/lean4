/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Internal.MonadAttach
public import Init.System.IO
import all Init.System.ST

instance : MonadAttach IO where
  CanReturn x a := ∃ world world', x world = .ok a world'
  attach x := fun world => match h : x world with
    | .ok a world' => .ok ⟨a, world, world', h⟩ world'
    | .error e world' => .error e world'

instance : LawfulMonadAttach IO where
  map_val_attach := by
    intro α x
    rw [funext_iff]
    intro world
    simp only [Functor.map, EST.bind, Function.comp_apply, MonadAttach.attach]
    split <;> rename_i heq
    · split at heq
      · cases heq
        simp_all [EST.pure]
      · cases heq
    · split at heq
      · cases heq
      · cases heq
        simp_all
