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
public import Init.Data.String.TakeDrop
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Std.Data.String.ToNat
import Init.Data.String.Lemmas.Pattern.TakeDrop.Basic
import Init.Data.String.Lemmas.Pattern.TakeDrop.Char
import Init.Data.Int.ToString

namespace String

namespace Slice

public theorem toInt?_eq_some_iff {s : String.Slice} {a : Int} :
    s.toInt? = some a ↔ (∃ b, s.toNat? = some b ∧ a = (b : Int)) ∨ ∃ t, s.copy = "-" ++ t ∧ ∃ b, t.toNat? = some b ∧ a = -(b : Int) := by
  rw [toInt?]
  match h : s.dropPrefix? '-' with
  | some rest =>
    have heq := eq_append_of_dropPrefix?_char_eq_some h
    suffices s.toNat? = none by
      simp only [Option.map_eq_some_iff, this, reduceCtorEq, false_and, exists_const, heq,
        ↓Char.isValue, String.reduceSingleton, append_right_inj, exists_eq_left', toNat?_copy,
        false_or]
      cases rest.toNat? <;> simp [Int.negOfNat_eq, eq_comm]
    exact toNat?_eq_none (by simp [← Bool.not_eq_true, isNat_iff, heq])
  | none =>
    simp only [↓Char.isValue, dropPrefix?_eq_none_iff, startsWith_char_eq_false_iff_forall_append,
      String.reduceSingleton, ne_eq] at h
    simp only [Option.map_eq_some_iff, Int.ofNat_eq_natCast, eq_comm (a := a), iff_self_or,
      forall_exists_index, and_imp]
    exact fun t ht => (h _ ht).elim

@[simp]
public theorem isSome_toInt? {s : String.Slice} : s.toInt?.isSome = s.isInt := by
  simp only [toInt?, ↓Char.isValue, isInt]
  split <;> simp

public theorem isInt_of_toInt?_eq_some {s : String.Slice} (h : s.toInt? = some a) : s.isInt = true := by
  simp [← isSome_toInt?, h]

@[simp]
public theorem toInt?_eq_none_iff {s : String.Slice} : s.toInt? = none ↔ s.isInt = false := by
  simp [← Option.isNone_iff_eq_none, ← Option.not_isSome, isSome_toInt?]

public theorem toInt?_eq_none {s : String.Slice} (h : s.isInt = false) : s.toInt? = none :=
  toInt?_eq_none_iff.2 h

public theorem isInt_iff {s : String.Slice} :
    s.isInt = true ↔ s.isNat = true ∨ ∃ t, s.copy = "-" ++ t ∧ t.isNat = true := by
  simp only [← isSome_toInt?, Option.isSome_iff_exists, toInt?_eq_some_iff, ← isSome_toNat?,
    ← String.isSome_toNat?]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, (⟨b, ⟨h, rfl⟩⟩|⟨t, ⟨h₁, ⟨b, ⟨h₂, rfl⟩⟩⟩⟩)⟩
    · simp [h]
    · exact Or.inr ⟨t, by simp [h₁, h₂]⟩
  · rintro (⟨a, h⟩|⟨t, h₁, ⟨b, h₂⟩⟩)
    · simp [h]
    · exact ⟨-(b : Int), Or.inr ⟨t, by simp [h₁, h₂]⟩⟩

public theorem isInt_of_isNat {s : String.Slice} (h : s.isNat = true) : s.isInt = true :=
  isInt_iff.2 (Or.inl h)

public theorem toInt?_eq_toNat?_of_startsWith_eq_false {s : String.Slice} (h : s.startsWith '-' = false) :
    s.toInt? = s.toNat?.map (fun (n : Nat) => (n : Int)) := by
  rw [toInt?, dropPrefix?_eq_none_iff.2 h]
  cases s.toNat? <;> simp

public theorem toInt?_eq_of_eq_minus_append {s : String.Slice} {t : String} (h : s.copy = "-" ++ t) :
    s.toInt? = t.toNat?.map (fun (n : Nat) => -(n : Int)) := by
  apply Option.ext (fun a => ?_)
  simp only [toInt?_eq_some_iff, h, append_right_inj, exists_eq_left']
  suffices s.toNat? = none by cases t.toNat? <;> simp [this, eq_comm]
  exact toNat?_eq_none (by simp [← Bool.not_eq_true, isNat_iff, h])

public theorem toInt?_eq_some_of_toNat?_eq_some {s : String.Slice} {a : Nat}
    (h : s.toNat? = some a) : s.toInt? = some (a : Int) :=
  toInt?_eq_some_iff.2 (Or.inl ⟨a, h, rfl⟩)

public theorem toInt?_congr {s t : String.Slice} (h : s.copy = t.copy) : s.toInt? = t.toInt? :=
  Option.ext (fun a => by simp [toInt?_eq_some_iff, toNat?_congr h, h])

public theorem isInt_congr {s t : String.Slice} (h : s.copy = t.copy) : s.isInt = t.isInt := by
  simp only [← isSome_toInt?, toInt?_congr h]

end Slice

@[simp]
public theorem isInt_toSlice {s : String} : s.toSlice.isInt = s.isInt :=
  (rfl)

@[simp]
public theorem isInt_comp_toSlice : String.Slice.isInt ∘ String.toSlice = String.isInt := by
  ext; simp

@[simp]
public theorem toInt?_toSlice {s : String} : s.toSlice.toInt? = s.toInt? :=
  (rfl)

@[simp]
public theorem toInt?_comp_toSlice : String.Slice.toInt? ∘ String.toSlice = String.toInt? := by
  ext; simp

@[simp]
public theorem Slice.isInt_copy {s : Slice} : s.copy.isInt = s.isInt := by
  simpa [← isInt_toSlice] using Slice.isInt_congr (by simp)

@[simp]
public theorem Slice.isInt_comp_copy : String.isInt ∘ String.Slice.copy = String.Slice.isInt := by
  ext; simp

@[simp]
public theorem Slice.toInt?_copy {s : Slice} : s.copy.toInt? = s.toInt? := by
  simpa [← isInt_toSlice] using Slice.toInt?_congr (by simp)

@[simp]
public theorem Slice.toInt?_comp_copy : String.toInt? ∘ String.Slice.copy = String.Slice.toInt? := by
  ext; simp

public theorem toInt?_eq_some_iff {s : String} {a : Int} :
    s.toInt? = some a ↔ (∃ b, s.toNat? = some b ∧ a = (b : Int)) ∨ ∃ t, s = "-" ++ t ∧ ∃ b, t.toNat? = some b ∧ a = -(b : Int) := by
  simp [← toInt?_toSlice, Slice.toInt?_eq_some_iff]

@[simp]
public theorem isSome_toInt? {s : String} : s.toInt?.isSome = s.isInt := by
  simp [← toInt?_toSlice, ← isInt_toSlice]

public theorem isInt_of_toInt?_eq_some {s : String} (h : s.toInt? = some a) : s.isInt = true := by
  rw [← isInt_toSlice, Slice.isInt_of_toInt?_eq_some (by simpa)]

@[simp]
public theorem toInt?_eq_none_iff {s : String} : s.toInt? = none ↔ s.isInt = false := by
  simp [← Option.isNone_iff_eq_none, ← Option.not_isSome, isSome_toInt?]

public theorem toInt?_eq_none {s : String} (h : s.isInt = false) : s.toInt? = none :=
  toInt?_eq_none_iff.2 h

public theorem isInt_iff {s : String} :
    s.isInt = true ↔ s.isNat = true ∨ ∃ t, s = "-" ++ t ∧ t.isNat = true := by
  simp [← isInt_toSlice, Slice.isInt_iff]

public theorem isInt_of_isNat {s : String} (h : s.isNat = true) : s.isInt = true := by
  rw [← isInt_toSlice, Slice.isInt_of_isNat (by simpa)]

public theorem toInt?_eq_toNat?_of_startsWith_eq_false {s : String} (h : s.startsWith '-' = false) :
    s.toInt? = s.toNat?.map (fun (a : Nat) => (a : Int)) := by
  rw [← toInt?_toSlice, ← toNat?_toSlice,
    Slice.toInt?_eq_toNat?_of_startsWith_eq_false (by simpa [← startsWith_eq_startsWith_toSlice])]

@[simp]
public theorem toInt?_minus_append {s : String} :
    ("-" ++ s).toInt? = s.toNat?.map (fun (n : Nat) => -(n : Int)) := by
  rw [← toInt?_toSlice, Slice.toInt?_eq_of_eq_minus_append]
  simp

public theorem toInt?_eq_some_of_toNat?_eq_some {s : String} {a : Nat} (h : s.toNat? = some a) :
    s.toInt? = some (a : Int) :=
  toInt?_eq_some_iff.2 (Or.inl ⟨a, h, rfl⟩)

end String

@[simp]
public theorem Nat.toInt?_repr (n : Nat) : n.repr.toInt? = some (n : Int) :=
  String.toInt?_eq_some_of_toNat?_eq_some (toNat?_repr _)

@[simp]
public theorem Nat.isInt_repr (n : Nat) : n.repr.isInt = true := by
  simp [← String.isSome_toInt?]

namespace Int

@[simp]
public theorem toInt?_repr (a : Int) : a.repr.toInt? = some a := by
  rw [repr_eq_if]
  split <;> (simp; omega)

@[simp]
public theorem isInt_repr (a : Int) : a.repr.isInt = true := by
  simp [← String.isSome_toInt?]

public theorem repr_injective {a b : Int} (h : Int.repr a = Int.repr b) : a = b := by
  rw [← Option.some.injEq, ← toInt?_repr a, ← toInt?_repr b, h]

@[simp]
public theorem repr_inj {a b : Int} : Int.repr a = Int.repr b ↔ a = b :=
  ⟨repr_injective, (· ▸ rfl)⟩

end Int
