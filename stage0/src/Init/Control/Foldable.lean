/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core

/-
  Typeclass for the polymorphic `foldlM` operation described in the paper.
  Remark:
  - `γ` is a "container" type of elements of type `α`.
  - `α` is treated as an output parameter by the typeclass resolution procedure.
    That is, it tries to find an instance using only `m` and `γ`.
-/
class Foldable (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
  foldlM [Monad m] : (δ → α → m δ) → δ → γ → m δ

-- Add the alias `foldlM` for `Foldable.foldlM`
export Foldable (foldlM)
