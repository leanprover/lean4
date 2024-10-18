/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Char.Lemmas

namespace String

protected theorem data_eq_of_eq {a b : String} (h : a = b) : a.data = b.data :=
  h ▸ rfl
protected theorem ne_of_data_ne {a b : String} (h : a.data ≠ b.data) : a ≠ b :=
  fun h' => absurd (String.data_eq_of_eq h') h
@[simp] protected theorem lt_irrefl (s : String) : ¬ s < s :=
  List.lt_irrefl Char.lt_irrefl s.data
protected theorem ne_of_lt {a b : String} (h : a < b) : a ≠ b := by
  have := String.lt_irrefl a
  intro h; subst h; contradiction

end String
