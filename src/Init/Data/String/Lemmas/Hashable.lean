/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.LawfulHashable
import all Init.Data.String.Slice
import Init.Data.String.Lemmas.Slice

namespace String

public theorem hash_eq {s : String} : hash s = String.hash s := rfl

namespace Slice

public theorem hash_eq {s : String.Slice} : hash s = String.hash s.copy := (rfl)

public instance : LawfulHashable String.Slice where
  hash_eq a b hab := by simp [hash_eq, beq_eq_true_iff.1 hab]

end String.Slice
