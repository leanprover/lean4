/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Array.Basic
public import Init.Data.Int.DivMod.Lemmas
public import Init.Omega

public section
universe u v

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- We do not use `linter.indexVariables` here as it is helpful to name the index variables as `lo`, `mid`, and `hi`.

namespace Array

@[specialize] def binSearchAux {α : Type u} {β : Type v} (lt : α → α → Bool) (found : Option α → β) (as : Array α) (k : α) :
    (lo : Fin (as.size + 1)) → (hi : Fin as.size) → (lo.1 ≤ hi.1) → β
  | lo, hi, h =>
    let m := (lo.1 + hi.1)/2
    let a := as[m]
    if lt a k then
      if h' : m + 1 ≤ hi.1 then
        binSearchAux lt found as k ⟨m+1, by omega⟩ hi h'
      else found none
    else if lt k a then
      if h' : m = 0 ∨ m - 1 < lo.1 then found none
      else binSearchAux lt found as k lo ⟨m-1, by omega⟩ (by simp; omega)
    else found (some a)
termination_by lo hi => hi.1 - lo.1

/--
Binary search for an element equivalent to `k` in the sorted array `as`. Returns the element from
the array, if it is found, or `none` otherwise.

The array `as` must be sorted according to the comparison operator `lt`, which should be a total
order.

The optional parameters `lo` and `hi` determine the region of the array indices to be searched. Both
are inclusive, and default to searching the entire array.
-/
@[inline] def binSearch {α : Type} (as : Array α) (k : α) (lt : α → α → Bool) (lo := 0) (hi := as.size - 1) : Option α :=
  if h : lo < as.size then
    let hi := if hi < as.size then hi else as.size - 1
    if w : lo ≤ hi then
      binSearchAux lt id as k ⟨lo, by omega⟩ ⟨hi, by simp [hi]; split <;> omega⟩ (by simp [hi]; omega)
    else
      none
  else
    none

/--
Binary search for an element equivalent to `k` in the sorted array `as`. Returns `true` if the
element is found, or `false` otherwise.

The array `as` must be sorted according to the comparison operator `lt`, which should be a total
order.

The optional parameters `lo` and `hi` determine the region of the array indices to be searched. Both
are inclusive, and default to searching the entire array.
-/
@[inline] def binSearchContains {α : Type} (as : Array α) (k : α) (lt : α → α → Bool) (lo := 0) (hi := as.size - 1) : Bool :=
  if h : lo < as.size then
    let hi := if hi < as.size then hi else as.size - 1
    if w : lo ≤ hi then
      binSearchAux lt Option.isSome as k ⟨lo, by omega⟩ ⟨hi, by simp [hi]; split <;> omega⟩ (by simp [hi]; omega)
    else
      false
  else
    false

@[specialize] private def binInsertAux {α : Type u} {m : Type u → Type v} [Monad m]
    (lt : α → α → Bool)
    (merge : α → m α)
    (add : Unit → m α)
    (as : Array α)
    (k : α) : (lo : Fin as.size) → (hi : Fin as.size) → (lo.1 ≤ hi.1) → (lt as[lo] k) → m (Array α)
  | lo, hi, h, w =>
    let mid    := (lo.1 + hi.1)/2
    let midVal := as[mid]
    if w₁ : lt midVal k then
      if h' : mid = lo then do let v ← add (); pure <| as.insertIdx (lo+1) v
      else binInsertAux lt merge add as k ⟨mid, by omega⟩ hi (by simp; omega) w₁
    else if w₂ : lt k midVal then
      have : mid ≠ lo := fun z => by simp [midVal, z] at w₁; simp_all
      binInsertAux lt merge add as k lo ⟨mid, by omega⟩ (by simp; omega) w
    else do
      as.modifyM mid <| fun v => merge v
termination_by lo hi => hi.1 - lo.1

/--
Inserts an element `k` into a sorted array `as` such that the resulting array is sorted.

The ordering predicate `lt` should be a total order on elements, and the array `as` should be sorted
with respect to `lt`.

If an element that `lt` equates to `k` is already present in `as`, then `merge` is applied to the
existing element to determine the value of that position in the resulting array. If no element equal
to `k` is present, then `add` is used to determine the value to be inserted.
-/
@[specialize] def binInsertM {α : Type u} {m : Type u → Type v} [Monad m]
    (lt : α → α → Bool)
    (merge : α → m α)
    (add : Unit → m α)
    (as : Array α)
    (k : α) : m (Array α) :=
  if h : as.size = 0 then do let v ← add (); pure <| as.push v
  else if lt k as[0] then do let v ← add (); pure <| as.insertIdx 0 v
  else if h' : !lt as[0] k then as.modifyM 0 <| merge
  else if lt as[as.size - 1] k then do let v ← add (); pure <| as.push v
  else if !lt k as[as.size - 1] then as.modifyM (as.size - 1) <| merge
  else binInsertAux lt merge add as k ⟨0, by omega⟩ ⟨as.size - 1, by omega⟩ (by simp) (by simpa using h')

/--
Inserts an element into a sorted array such that the resulting array is sorted. If the element is
already present in the array, it is not inserted.

The ordering predicate `lt` should be a total order on elements, and the array `as` should be sorted
with respect to `lt`.

`Array.binInsertM` is a more general operator that provides greater control over the handling of
duplicate elements in addition to running in a monad.

Examples:
* `#[0, 1, 3, 5].binInsert (· < ·) 2 = #[0, 1, 2, 3, 5]`
* `#[0, 1, 3, 5].binInsert (· < ·) 1 = #[0, 1, 3, 5]`
* `#[].binInsert (· < ·) 1 = #[1]`
-/
@[inline] def binInsert {α : Type u} (lt : α → α → Bool) (as : Array α) (k : α) : Array α :=
  Id.run <| binInsertM lt (fun _ => pure k) (fun _ => pure k) as k

end Array
