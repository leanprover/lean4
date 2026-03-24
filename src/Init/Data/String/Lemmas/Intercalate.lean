/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Defs
import all Init.Data.String.Defs
public import Init.Data.String.Slice
import all Init.Data.String.Slice
import Init.ByCases

public section

namespace String

@[simp]
theorem intercalate_nil {s : String} : s.intercalate [] = "" := by
  simp [intercalate]

@[simp]
theorem intercalate_singleton {s t : String} : s.intercalate [t] = t := by
  simp [intercalate, intercalate.go]

private theorem intercalateGo_append {s t u : String} {l : List String} :
    intercalate.go (s ++ t) u l = s ++ intercalate.go t u l := by
  induction l generalizing t <;> simp [intercalate.go, String.append_assoc, *]

@[simp]
theorem intercalate_cons_cons {s t u : String} {l : List String} :
    s.intercalate (t :: u :: l) = t ++ s ++ s.intercalate (u :: l) := by
  simp [intercalate, intercalate.go, intercalateGo_append]

@[simp]
theorem intercalate_cons_append {s t u : String} {l : List String} :
    s.intercalate ((t ++ u) :: l) = t ++ s.intercalate (u :: l) := by
  cases l <;> simp [String.append_assoc]

theorem intercalate_cons_of_ne_nil {s t : String} {l : List String} (h : l ≠ []) :
    s.intercalate (t :: l) = t ++ s ++ s.intercalate l :=
  match l, h with
  | u::l, _ => by simp

theorem intercalate_append_of_ne_nil {l m : List String} {s : String} (hl : l ≠ []) (hm : m ≠ []) :
    s.intercalate (l ++ m) = s.intercalate l ++ s ++ s.intercalate m := by
  induction l with
  | nil => simp_all
  | cons hd tl ih =>
    rw [List.cons_append, intercalate_cons_of_ne_nil (by simp_all)]
    by_cases ht : tl = []
    · simp_all
    · simp [ih ht, intercalate_cons_of_ne_nil ht, String.append_assoc]

@[simp]
theorem toList_intercalate {s : String} {l : List String} :
    (s.intercalate l).toList = s.toList.intercalate (l.map String.toList) := by
  induction l with
  | nil => simp
  | cons hd tl ih => cases tl <;> simp_all

namespace Slice

@[simp]
theorem _root_.String.appendSlice_eq {s : String} {t : Slice} : s ++ t = s ++ t.copy := rfl

private theorem intercalateGo_append {s t : String} {u : Slice} {l : List Slice} :
    intercalate.go (s ++ t) u l = s ++ intercalate.go t u l := by
  induction l generalizing t <;> simp [intercalate.go, String.append_assoc, *]

@[simp]
theorem intercalate_eq {s : Slice} {l : List Slice} :
    s.intercalate l = s.copy.intercalate (l.map Slice.copy) := by
  induction l with
  | nil => simp [intercalate]
  | cons hd tl ih => cases tl <;> simp_all [intercalate, intercalate.go, intercalateGo_append]

end Slice

end String
