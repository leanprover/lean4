/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Control.Basic

public class MonadAttach (m : Type u → Type v) where
  CanReturn {α : Type u} : m α → α → Prop
  attach {α : Type u} (x : m α) : m (Subtype (CanReturn x))

public class LawfulMonadAttach (m : Type u → Type v) [Monad m] [MonadAttach m] where
  map_attach {α : Type u} {x : m α} : Subtype.val <$> MonadAttach.attach x = x
  canReturn_map_imp {α : Type u} {P : α → Prop} {x : m (Subtype P)} {a : α} :
      MonadAttach.CanReturn (Subtype.val <$> x) a → P a

public def MonadAttach.pbind
    [Monad m] [MonadAttach m]
    (x : m α) (f : (a : α) → MonadAttach.CanReturn x a → m β) : m β :=
  MonadAttach.attach x >>= (fun ⟨a, ha⟩ => f a ha)
