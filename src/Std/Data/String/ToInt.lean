/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.String.Search
public import Init.Data.ToString.Extra
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Std.Data.String.ToNat
import Init.Data.String.Lemmas.Pattern.TakeDrop.Basic
import Init.Data.String.Lemmas.Pattern.TakeDrop.Char
import Init.Data.Int.ToString

namespace String

namespace Slice

public theorem isInt_iff {s : String.Slice} :
    s.isInt = true ↔ s.isNat ∨ ∃ t, s.copy = "-" ++ t ∧ t.isNat := by
  rw [isInt]
  match h : s.dropPrefix? '-' with
  | some rest =>
    have heq := eq_append_of_dropPrefix?_char_eq_some h
    suffices s.isNat = false by simp [this, heq]
    simp [← Bool.not_eq_true, isNat_iff, heq]
  | none =>
    simp only [↓Char.isValue, dropPrefix?_eq_none_iff, startsWith_char_eq_false_iff_forall_append,
      String.reduceSingleton, ne_eq] at h
    simpa using fun t ht => (h t ht).elim


end Slice

@[simp]
public theorem toInt?_minus_append {s : String} :
    ("-" ++ s).toInt? = s.toNat?.map (fun n => -(n : Int)) := sorry

end String

@[simp]
public theorem Nat.toInt?_repr {n : Nat} : n.repr.toInt? = some n := sorry

namespace Int

public theorem Int.toInt?_toString {a : Int} : (toString a).toInt? = some a := by
  rw [toString_eq_if]
  split <;> (simp; omega)

end Int
