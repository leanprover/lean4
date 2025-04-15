/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Alex Keizer
-/
prelude
import Lean.Expr

/-!
# `ToLevel` class
This module defines `Lean.ToLevel`, which is the `Lean.Level` analogue to `Lean.ToExpr`.
-/

namespace Lean

/-- A class to create `Level` expressions that denote particular universe levels in Lean.
`Lean.ToLevel.toLevel.{u}` evaluates to a `Lean.Level` term representing `u` -/
class ToLevel.{u} : Type where
  /-- A `Level` that represents the universe level `u`. -/
  toLevel : Level
  /-- A hack to avoid the "unused universe parameter" error.
    We can remove this field pending issue https://github.com/leanprover/lean4/issues/2116 -/
  univ : ∀ (_ : Sort u), True := fun _ => trivial
export ToLevel (toLevel)

instance : ToLevel.{0} where
  toLevel := .zero

instance [ToLevel.{u}] : ToLevel.{u+1} where
  toLevel := .succ toLevel.{u}

/-- `ToLevel` for `max u v`. This is not an instance since it causes divergence. -/
def ToLevel.max [ToLevel.{u}] [ToLevel.{v}] : ToLevel.{max u v} where
  toLevel := .max toLevel.{u} toLevel.{v}

/-- `ToLevel` for `imax u v`. This is not an instance since it causes divergence. -/
def ToLevel.imax [ToLevel.{u}] [ToLevel.{v}] : ToLevel.{imax u v} where
  toLevel := .imax toLevel.{u} toLevel.{v}

end Lean
