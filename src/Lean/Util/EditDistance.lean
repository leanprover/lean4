/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
prelude
import Init.Data.Range

namespace Lean.EditDistance

/--
Compute the Levenshtein distance between two strings, up to some cutoff.

If the return value is `none`, then the distance is certainly greater than the cutoff value, but a
returned `some` does not necessarily indicate that the edit distance is less than or equal to the
cutoff.
-/
def levenshtein (str1 str2 : String) (cutoff : Nat) : Option Nat := Id.run do
  let len1 := str1.length
  let len2 := str2.length
  if max len1 len2 - min len1 len2 > cutoff then return none

  let mut v0 := Array.mkArray (len2 + 1) 0
  let mut v1 := v0

  for i in [0:v0.size] do
    v0 := v0.set! i i
  let mut iter1 := str1.iter
  for i in [0:str1.length] do
    v1 :=v1.set! 0 (i+1)
    let mut iter2 := str2.iter
    for j in [0:len2] do
      let deletionCost := v0[j+1]! + 1
      let insertionCost := v1[j]! + 1
      let substCost :=
        if iter1.curr == iter2.curr then v0[j]!
        else v0[j]! + 1
      let cost := min (min deletionCost insertionCost) substCost
      v1 := v1.set! (j+1) cost
      iter2 := iter2.next
    iter1 := iter1.next
    if v1.all (· > cutoff) then return none
    v0 := v1
  some v0[len2]!
