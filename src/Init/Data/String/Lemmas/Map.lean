/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Modify
import all Init.Data.String.Modify

namespace String

theorem ofList_nil : ofList [] = "" := by
  simp [← toList_inj]

theorem toList_mapAux {f : Char → Char} {s : String} {p : s.ValidPos}
    (h : p.Splits t₁ t₂) : mapAux f s p = t₁ ++ ofList (t₂.toList.map f) := by
  fun_induction mapAux  generalizing t₁ t₂ with
  | case1 s => simp_all
  | case2 => sorry



end String
