/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Core

public section

deriving instance DecidableEq for PLift

instance [Subsingleton α] : Subsingleton (PLift α) where
  allEq := fun ⟨a⟩ ⟨b⟩ => congrArg PLift.up (Subsingleton.elim a b)
