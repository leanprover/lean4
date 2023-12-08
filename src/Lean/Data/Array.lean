/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

import Init.Data.Array

namespace Array

/-!
This module contains utility functions involving Arrays that are useful in a few places
of the lean code base, but too specialized to live in `Init.Data.Array`, which arguably
is part of the public, user-facing standard library.
-/

/--
Given an array `a`, runs `f xᵢ xⱼ` for all `i < j`, removes those entries for which `f` returns
`false` (and will subsequently skip pairs if one element is removed), and returns the array of
remaining elements.

This can be used to remove elements from an array where a “better” element, in some partial
order, exists in the array.
-/
def filterPairsM {m} [Monad m] {α} (a : Array α) (f : α → α → m (Bool × Bool)) :
    m (Array α) := do
  let mut removed := Array.mkArray a.size false
  let mut numRemoved := 0
  for h1 : i in [:a.size] do for h2 : j in [i+1:a.size] do
    unless removed[i]! || removed[j]! do
      let xi := a[i]'h1.2
      let xj := a[j]'h2.2
      let (keepi, keepj) ← f xi xj
      unless keepi do
        numRemoved := numRemoved + 1
        removed := removed.set! i true
      unless keepj do
        numRemoved := numRemoved + 1
        removed := removed.set! j true
  let mut a' := Array.mkEmpty numRemoved
  for h : i in [:a.size] do
    unless removed[i]! do
      a' := a'.push (a[i]'h.2)
  return a'

end Array
