/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.System.IO

public class MonadAttach (m : Type u → Type v) [Monad m] where
  CanReturn : m α → α → Prop
  attach : (x : m α) → m (Subtype (CanReturn x))
  map_val_attach : Subtype.val <$> attach x = x

public class LawfulMonadAttach (m : Type u → Type v) [Monad m] [MonadAttach m] where
  strongest {P : α → Prop} {x : m (Subtype P)} {a : α} :
    MonadAttach.CanReturn (Subtype.val <$> x) a → P a
  ump {P : α → Prop} {x : m (Subtype P)} :
    (fun x => ⟨x.val, strongest x.property⟩) <$> MonadAttach.attach (Subtype.val <$> x) = x

instance : MonadAttach IO where
  CanReturn x a := ∃ world world', x world = .ok a world'
  attach x := fun world => match (x world)
