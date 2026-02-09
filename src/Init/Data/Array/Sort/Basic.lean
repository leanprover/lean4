/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Array.Subarray.Split
public import Init.Data.Slice.Array

-- TODO
import all Init.Data.Array.Subarray
import all Init.Data.Array.Subarray.Split
import Init.Data.Array.Lemmas
-- import Init

public section

-- TODO
@[simp, grind =]
theorem Subarray.size_drop {xs : Subarray α} {n : Nat} :
    (xs.drop n).size = xs.size - n := by
  simp only [size, stop, drop, start]
  omega

@[grind =, simp]
theorem Subarray.size_mkSlice_rio {xs : Subarray α} :
    xs[*...i].size = min i xs.size := by
  simp [← Subarray.size_toArray]

@[grind =, simp]
theorem Subarray.size_mkSlice_rci {xs : Subarray α} :
    xs[i...*].size = xs.size - i := by
  simp [← Subarray.size_toArray]

private def Array.MergeSort.Internal.merge (xs ys : Array α) (le : α → α → Bool := by exact (· ≤ ·)) :
    Array α :=
  if hxs : 0 < xs.size then
    if hys : 0 < ys.size then
      go xs[*...*] ys[*...*] (by simp only [Array.size_mkSlice_rii]; omega) (by simp only [Array.size_mkSlice_rii]; omega) (Array.emptyWithCapacity (xs.size + ys.size))
    else
      xs
  else
    ys
where
  go (xs ys : Subarray α) (hxs : 0 < xs.size) (hys : 0 < ys.size) (acc : Array α) : Array α :=
    let x := xs[0]
    let y := ys[0]
    if le x y then
      if hi : 1 < xs.size then
        go (xs.drop 1) ys (by simp only [Subarray.size_drop]; omega) hys (acc.push x)
      else
        ys.foldl (init := acc.push x) (fun acc y => acc.push y)
    else
      if hj : 1 < ys.size then
        go xs (ys.drop 1) hxs (by simp only [Subarray.size_drop]; omega) (acc.push y)
      else
        xs.foldl (init := acc.push y) (fun acc x => acc.push x)
  termination_by xs.size + ys.size

def Subarray.mergeSort (xs : Subarray α) (le : α → α → Bool := by exact (· ≤ ·)) : Array α :=
    if h : 1 < xs.size then
      let splitIdx := (xs.size + 1) / 2 -- We follow the same splitting convention as `List.mergeSort`
      let left := xs[*...splitIdx]
      let right := xs[splitIdx...*]
      Array.MergeSort.Internal.merge (mergeSort left le) (mergeSort right le) le
    else
      xs.toArray
termination_by xs.size
decreasing_by
  · simp only [Subarray.size_mkSlice_rio]; omega
  · simp only [Subarray.size_mkSlice_rci]; omega

@[inline]
def Array.mergeSort (xs : Array α) (le : α → α → Bool := by exact (· ≤ ·)) : Array α :=
    xs[*...*].mergeSort le
