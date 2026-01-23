/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Grind
public import Init.Data.String

public section

/-!
# LowerCase

This module provides predicates and normalization functions to handle ASCII case-insensitivity. It
includes proofs of idempotency for lowercase transformations and utilities for validating lowercase
state `String`.
-/

namespace Std.Http.Internal

set_option linter.all true

/--
Predicate asserting that a string is already in lowercase normal form.
-/
abbrev IsLowerCase (s : String) : Prop :=
  s.toLower = s

namespace IsLowerCase

private theorem Char.toLower_idempotent (c : Char) : c.toLower.toLower = c.toLower := by
  grind [Char.toLower]

/--
Proof that applying `toLower` to any string results in a string that satisfies the `IsLowerCase`
predicate.
-/
theorem isLowerCase_toLower {s : String} : IsLowerCase s.toLower := by
  unfold IsLowerCase String.toLower
  exact String.map_idempotent Char.toLower_idempotent

theorem isLowerCase_empty : IsLowerCase "" := by
  simp [IsLowerCase, String.toLower]

end Std.Http.Internal.IsLowerCase
