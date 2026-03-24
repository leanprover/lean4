/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia Markus Himmel
-/
module

prelude
public import Init.Data.String.Iter.Intercalate
public import Init.Data.String.Slice
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Defs
import Init.Data.String.Lemmas.Intercalate
import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Combinators.FilterMap

namespace Std.Iter

@[simp]
public theorem joinString_eq {α β : Type} [Std.Iterator α Id β] [Std.Iterators.Finite α Id]
    [ToString β] {it : Std.Iter (α := α) β} :
    it.joinString = String.join (it.toList.map toString) := by
  rw [joinString, String.join, ← foldl_toList, toList_map]

@[simp]
public theorem intercalateString_eq {α β : Type} [Std.Iterator α Id β] [Std.Iterators.Finite α Id]
    [ToString β] {s : String.Slice} {it : Std.Iter (α := α) β} :
    it.intercalateString s = s.copy.intercalate (it.toList.map toString) := by
  simp only [intercalateString, String.appendSlice_eq, ← foldl_toList, toList_map]
  generalize s.copy = s
  suffices ∀ (l m : List String),
      (l.foldl (init := if m = [] then none else some (s.intercalate m))
        (fun | none, sl => some sl | some str, sl => some (str ++ s ++ sl))).getD ""
        = s.intercalate (m ++ l) by
    simpa [-foldl_toList] using this (it.toList.map toString) []
  intro l m
  induction l generalizing m with
  | nil => cases m <;> simp
  | cons hd tl ih =>
    rw [List.append_cons, ← ih, List.foldl_cons]
    congr
    simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false, ↓reduceIte]
    match m with
    | [] => simp
    | x::xs =>
      simp only [reduceCtorEq, ↓reduceIte, List.cons_append, Option.some.injEq]
      rw [← List.cons_append, String.intercalate_append_of_ne_nil (by simp) (by simp),
        String.intercalate_singleton]

end Std.Iter
