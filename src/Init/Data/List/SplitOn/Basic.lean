/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.List.Basic
public import Init.NotationExtra
import Init.Data.Array.Bootstrap
import Init.Data.List.Lemmas

public section

set_option doc.verso true

namespace List

/--
Split a list at every element satisfying a predicate, and then prepend {lean}`acc.reverse` to the
first element of the result.

* {lean}`[1, 1, 2, 3, 2, 4, 4].splitOnPPrepend (· == 2) [0, 5] = [[5, 0, 1, 1], [3], [4, 4]]`
-/
noncomputable def splitOnPPrepend (p : α → Bool) : (l : List α) → (acc : List α) → List (List α)
| [], acc => [acc.reverse]
| a :: t, acc => if p a then acc.reverse :: splitOnPPrepend p t [] else splitOnPPrepend p t (a::acc)

/--
Split a list at every element satisfying a predicate. The separators are not in the result.

Examples:
* {lean}`[1, 1, 2, 3, 2, 4, 4].splitOnP (· == 2) = [[1, 1], [3], [4, 4]]`
-/
noncomputable def splitOnP (p : α → Bool) (l : List α) : List (List α) :=
  splitOnPPrepend p l []

@[deprecated splitOnPPrepend (since := "2026-02-26")]
noncomputable def splitOnP.go (p : α → Bool) (l acc : List α) : List (List α) :=
  splitOnPPrepend p l acc

/-- Tail recursive version of {name}`splitOnP`. -/
@[inline]
def splitOnPTR (p : α → Bool) (l : List α) : List (List α) := go l #[] #[] where
  @[specialize] go : List α → Array α → Array (List α) → List (List α)
  | [], acc, r => r.toListAppend [acc.toList]
  | a :: t, acc, r => bif p a then go t #[] (r.push acc.toList) else go t (acc.push a) r

@[csimp] theorem splitOnP_eq_splitOnPTR : @splitOnP = @splitOnPTR := by
  funext α P l
  simp only [splitOnPTR]
  suffices ∀ xs acc r,
    splitOnPTR.go P xs acc r = r.toList ++ splitOnPPrepend P xs acc.toList.reverse from
      (this l #[] #[]).symm
  intro xs acc r
  induction xs generalizing acc r with
  | nil => simp [splitOnPPrepend, splitOnPTR.go]
  | cons x xs IH => cases h : P x <;> simp [splitOnPPrepend, splitOnPTR.go, *]

/--
Split a list at every occurrence of a separator element. The separators are not in the result.

Examples:
* {lean}`[1, 1, 2, 3, 2, 4, 4].splitOn 2 = [[1, 1], [3], [4, 4]]`
-/
@[inline] def splitOn [BEq α] (a : α) (as : List α) : List (List α) :=
  as.splitOnP (· == a)

end List
