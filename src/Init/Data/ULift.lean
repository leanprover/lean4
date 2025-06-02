/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Core

deriving instance DecidableEq for ULift

instance [Subsingleton α] : Subsingleton (ULift α) where
  allEq := fun ⟨a⟩ ⟨b⟩ => congrArg ULift.up (Subsingleton.elim a b)
