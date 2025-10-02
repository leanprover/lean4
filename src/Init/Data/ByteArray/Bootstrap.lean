/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.List.Basic

public section
set_option doc.verso true

namespace ByteArray

@[simp]
theorem data_push {a : ByteArray} {b : UInt8} : (a.push b).data = a.data.push b := rfl

/--
Appends two byte arrays.

In compiled code, calls to {name}`ByteArray.append` are replaced with the much more efficient
{name (scope:="Init.Data.ByteArray.Basic")}`ByteArray.fastAppend`.
-/
@[expose]
protected def append (a b : ByteArray) : ByteArray :=
  ⟨⟨a.data.toList ++ b.data.toList⟩⟩

@[simp]
theorem toList_data_append' {a b : ByteArray} :
    (a.append b).data.toList = a.data.toList ++ b.data.toList := by
  have ⟨⟨a⟩⟩ := a
  have ⟨⟨b⟩⟩ := b
  rfl

theorem ext : {x y : ByteArray} → x.data = y.data → x = y
  | ⟨_⟩, ⟨_⟩, rfl => rfl

end ByteArray

@[simp]
theorem List.toList_data_toByteArray {l : List UInt8} :
    l.toByteArray.data.toList = l := by
  rw [List.toByteArray]
  suffices ∀ a b, (List.toByteArray.loop a b).data.toList = b.data.toList ++ a by
    simpa using this l ByteArray.empty
  intro a b
  fun_induction List.toByteArray.loop a b with simp_all [toList_push]
where
  toList_push {xs : Array UInt8} {x : UInt8} : (xs.push x).toList = xs.toList ++ [x] := by
    have ⟨xs⟩ := xs
    simp [Array.push, List.concat_eq_append]

theorem List.toByteArray_append' {l l' : List UInt8} :
    (l ++ l').toByteArray = l.toByteArray.append l'.toByteArray :=
  ByteArray.ext (ext (by simp))
where
  ext : {x y : Array UInt8} → x.toList = y.toList → x = y
  | ⟨_⟩, ⟨_⟩, rfl => rfl
