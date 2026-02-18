/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Iterate
import Init.Data.Char.Lemmas

public section

namespace String

/--
Returns the length of a string in Unicode code points.

Examples:
* `"".length = 0`
* `"abc".length = 3`
* `"L∃∀N".length = 4`
-/
@[extern "lean_string_length", expose, tagged_return]
def length (b : @& String) : Nat :=
  b.toList.length

@[simp]
theorem Internal.size_toArray {b : String} : (String.Internal.toArray b).size = b.length :=
  (rfl)

@[simp]
theorem length_toList {s : String} : s.toList.length = s.length := (rfl)

@[deprecated String.length_toList (since := "2025-10-30")]
theorem length_data {b : String} : b.toList.length = b.length := (rfl)

@[simp]
theorem length_ofList {l : List Char} : (String.ofList l).length = l.length := by
  rw [← String.length_toList, String.toList_ofList]

@[deprecated String.length_ofList (since := "2025-10-30")]
theorem _root_.List.length_asString {l : List Char} : (String.ofList l).length = l.length :=
  String.length_ofList

@[simp] theorem length_empty : "".length = 0 := by simp [← length_toList, toList_empty]

@[simp]
theorem length_singleton {c : Char} : (String.singleton c).length = 1 := by
  simp [← length_toList]

@[simp] theorem length_push (c : Char) : (String.push s c).length = s.length + 1 := by
  simp [← length_toList]

@[simp] theorem length_pushn (c : Char) (n : Nat) : (pushn s c n).length = s.length + n := by
  rw [pushn_eq_repeat_push]; induction n <;> simp [Nat.repeat, Nat.add_assoc, *]

@[simp] theorem length_append (s t : String) : (s ++ t).length = s.length + t.length := by
  simp [← length_toList]

@[deprecated String.length_singleton (since := "2026-02-12")]
theorem _root_.Char.length_toString (c : Char) : c.toString.length = 1 := by
  simp

end String
