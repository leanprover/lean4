/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Core

deriving instance DecidableEq for PLift

instance [Subsingleton α] : Subsingleton (PLift α) where
  allEq := fun ⟨a⟩ ⟨b⟩ => congrArg PLift.up (Subsingleton.elim a b)
