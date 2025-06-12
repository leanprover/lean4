/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Data.Array.Bootstrap

/-!
## Tail recursive implementations for `List` definitions.

Many of the proofs require theorems about `Array`,
so these are in a separate file to minimize imports.

If you import `Init.Data.List.Basic` but do not import this file,
then at runtime you will get non-tail recursive versions of the following definitions.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/-! ## Basic `List` operations.

The following operations are already tail-recursive, and do not need `@[csimp]` replacements:
`get`, `foldl`, `beq`, `isEqv`, `reverse`, `elem` (and hence `contains`), `drop`, `dropWhile`,
`partition`, `isPrefixOf`, `isPrefixOf?`, `find?`, `findSome?`, `lookup`, `any` (and hence `or`),
`all` (and hence `and`) , `range`, `eraseDups`, `eraseReps`, `span`, `splitBy`.

The following operations are still missing `@[csimp]` replacements:
`concat`, `zipWithAll`.

The following operations are not recursive to begin with
(or are defined in terms of recursive primitives):
`isEmpty`, `isSuffixOf`, `isSuffixOf?`, `rotateLeft`, `rotateRight`, `insert`, `zip`, `enum`,
`min?`, `max?`, and `removeAll`.

The following operations were already given `@[csimp]` replacements in `Init/Data/List/Basic.lean`:
`length`, `map`, `filter`, `replicate`, `leftPad`, `unzip`, `range'`, `iota`, `intersperse`.

The following operations are given `@[csimp]` replacements below:
`set`, `filterMap`, `foldr`, `append`, `bind`, `join`,
`take`, `takeWhile`, `dropLast`, `replace`, `modify`, `insertIdx`, `erase`, `eraseIdx`, `zipWith`,
`enumFrom`, and `intercalate`.

-/


/-! ### set -/

/--
Replaces the value at (zero-based) index `n` in `l` with `a`. If the index is out of bounds, then
the list is returned unmodified.

This is a tail-recursive version of `List.set` that's used at runtime.

Examples:
* `["water", "coffee", "soda", "juice"].set 1 "tea" = ["water", "tea", "soda", "juice"]`
* `["water", "coffee", "soda", "juice"].set 4 "tea" = ["water", "coffee", "soda", "juice"]`
-/
@[inline] def setTR (l : List α) (n : Nat) (a : α) : List α := go l n #[] where
  /-- Auxiliary for `setTR`: `setTR.go l a xs n acc = acc.toList ++ set xs a`,
  unless `n ≥ l.length` in which case it returns `l` -/
  go : List α → Nat → Array α → List α
  | [], _, _ => l
  | _::xs, 0, acc => acc.toListAppend (a::xs)
  | x::xs, n+1, acc => go xs n (acc.push x)

@[csimp] theorem set_eq_setTR : @set = @setTR := by
  funext α l n a; simp [setTR]
  let rec go (acc) : ∀ xs i, l = acc.toList ++ xs →
    setTR.go l a xs i acc = acc.toList ++ xs.set i a
  | [], _ => fun h => by simp [setTR.go, set, h]
  | x::xs, 0 => by simp [setTR.go, set]
  | x::xs, n+1 => fun h => by simp only [setTR.go, set]; rw [go _ xs] <;> simp [h]
  exact (go #[] _ _ rfl).symm

/-! ### filterMap -/


/--
Applies a function that returns an `Option` to each element of a list, collecting the non-`none`
values.

`O(|l|)`. This is a tail-recursive version of `List.filterMap`, used at runtime.

Example:
```lean example
#eval [1, 2, 5, 2, 7, 7].filterMapTR fun x =>
  if x > 2 then some (2 * x) else none
```
```output
[10, 14, 14]
```
-/
@[inline] def filterMapTR (f : α → Option β) (l : List α) : List β := go l #[] where
  /-- Auxiliary for `filterMap`: `filterMap.go f l = acc.toList ++ filterMap f l` -/
  @[specialize] go : List α → Array β → List β
  | [], acc => acc.toList
  | a::as, acc => match f a with
    | none => go as acc
    | some b => go as (acc.push b)

@[csimp] theorem filterMap_eq_filterMapTR : @List.filterMap = @filterMapTR := by
  funext α β f l
  let rec go : ∀ as acc, filterMapTR.go f as acc = acc.toList ++ as.filterMap f
    | [], acc => by simp [filterMapTR.go, filterMap]
    | a::as, acc => by
      simp only [filterMapTR.go, go as, Array.toList_push, append_assoc, singleton_append,
        filterMap]
      split <;> simp [*]
  exact (go l #[]).symm

/-! ### foldr -/

/--
Folds a function over a list from the right, accumulating a value starting with `init`. The
accumulated value is combined with the each element of the list in reverse order, using `f`.

`O(|l|)`. This is the tail-recursive replacement for `List.foldr` in runtime code.

Examples:
 * `[a, b, c].foldrTR f init  = f a (f b (f c init))`
 * `[1, 2, 3].foldrTR (toString · ++ ·) "" = "123"`
 * `[1, 2, 3].foldrTR (s!"({·} {·})") "!" = "(1 (2 (3 !)))"`
-/
@[specialize] def foldrTR (f : α → β → β) (init : β) (l : List α) : β := l.toArray.foldr f init

@[csimp] theorem foldr_eq_foldrTR : @foldr = @foldrTR := by
  funext α β f init l; simp only [foldrTR, ← Array.foldr_toList]

/-! ### flatMap  -/

/--
Applies a function that returns a list to each element of a list, and concatenates the resulting
lists.

This is the tail-recursive version of `List.flatMap` that's used at runtime.

Examples:
* `[2, 3, 2].flatMapTR List.range = [0, 1, 0, 1, 2, 0, 1]`
* `["red", "blue"].flatMapTR String.toList = ['r', 'e', 'd', 'b', 'l', 'u', 'e']`
-/
@[inline] def flatMapTR (f : α → List β) (as : List α) : List β := go as #[] where
  /-- Auxiliary for `flatMap`: `flatMap.go f as = acc.toList ++ bind f as` -/
  @[specialize] go : List α → Array β → List β
  | [], acc => acc.toList
  | x::xs, acc => go xs (acc ++ f x)

@[csimp] theorem flatMap_eq_flatMapTR : @List.flatMap = @flatMapTR := by
  funext α β f as
  let rec go : ∀ as acc, flatMapTR.go f as acc = acc.toList ++ as.flatMap f
    | [], acc => by simp [flatMapTR.go, flatMap]
    | x::xs, acc => by simp [flatMapTR.go, flatMap, go xs]
  exact (go as #[]).symm

/-! ### flatten -/

/--
Concatenates a list of lists into a single list, preserving the order of the elements.

`O(|flatten L|)`. This is a tail-recursive version of `List.flatten`, used in runtime code.

Examples:
* `[["a"], ["b", "c"]].flattenTR = ["a", "b", "c"]`
* `[["a"], [], ["b", "c"], ["d", "e", "f"]].flattenTR = ["a", "b", "c", "d", "e", "f"]`
-/
@[inline] def flattenTR (l : List (List α)) : List α := l.flatMapTR id

@[csimp] theorem flatten_eq_flattenTR : @flatten = @flattenTR := by
  funext α l; rw [← List.flatMap_id, List.flatMap_eq_flatMapTR]; rfl

/-! ## Sublists -/

/-! ### take -/

/--
Extracts the first `n` elements of `xs`, or the whole list if `n` is greater than `xs.length`.

`O(min n |xs|)`. This is a tail-recursive version of `List.take`, used at runtime.

Examples:
* `[a, b, c, d, e].takeTR 0 = []`
* `[a, b, c, d, e].takeTR 3 = [a, b, c]`
* `[a, b, c, d, e].takeTR 6 = [a, b, c, d, e]`
-/
@[inline] def takeTR (n : Nat) (l : List α) : List α := go l n #[] where
  /-- Auxiliary for `take`: `take.go l xs n acc = acc.toList ++ take n xs`,
  unless `n ≥ xs.length` in which case it returns `l`. -/
  @[specialize] go : List α → Nat → Array α → List α
  | [], _, _ => l
  | _::_, 0, acc => acc.toList
  | a::as, n+1, acc => go as n (acc.push a)

@[csimp] theorem take_eq_takeTR : @take = @takeTR := by
  funext α i l; simp [takeTR]
  suffices ∀ xs acc, l = acc.toList ++ xs → takeTR.go l xs i acc = acc.toList ++ xs.take i from
    (this l #[] (by simp)).symm
  intro xs; induction xs generalizing i with intro acc
  | nil => cases i <;> simp [take, takeTR.go]
  | cons x xs IH =>
    cases i with simp only [take, takeTR.go]
    | zero => simp
    | succ n => intro h; rw [IH] <;> simp_all

/-! ### takeWhile -/


/--
 Returns the longest initial segment of `xs` for which `p` returns true.

`O(|xs|)`. This is a tail-recursive version of `List.take`, used at runtime.

Examples:
* `[7, 6, 4, 8].takeWhileTR (· > 5) = [7, 6]`
* `[7, 6, 6, 5].takeWhileTR (· > 5) = [7, 6, 6]`
* `[7, 6, 6, 8].takeWhileTR (· > 5) = [7, 6, 6, 8]`
-/
@[inline] def takeWhileTR (p : α → Bool) (l : List α) : List α := go l #[] where
  /-- Auxiliary for `takeWhile`: `takeWhile.go p l xs acc = acc.toList ++ takeWhile p xs`,
  unless no element satisfying `p` is found in `xs` in which case it returns `l`. -/
  @[specialize] go : List α → Array α → List α
  | [], _ => l
  | a::as, acc => bif p a then go as (acc.push a) else acc.toList

@[csimp] theorem takeWhile_eq_takeWhileTR : @takeWhile = @takeWhileTR := by
  funext α p l; simp [takeWhileTR]
  suffices ∀ xs acc, l = acc.toList ++ xs →
      takeWhileTR.go p l xs acc = acc.toList ++ xs.takeWhile p from
    (this l #[] (by simp)).symm
  intro xs; induction xs with intro acc
  | nil => simp [takeWhile, takeWhileTR.go]
  | cons x xs IH =>
    simp only [takeWhileTR.go, Array.toListImpl_eq, takeWhile]
    split
    · intro h; rw [IH] <;> simp_all
    · simp [*]

/-! ### dropLast -/

/--
Removes the last element of the list, if one exists.

This is a tail-recursive version of `List.dropLast`, used at runtime.

Examples:
* `[].dropLastTR = []`
* `["tea"].dropLastTR = []`
* `["tea", "coffee", "juice"].dropLastTR = ["tea", "coffee"]`
-/
@[inline] def dropLastTR (l : List α) : List α := l.toArray.pop.toList

@[csimp] theorem dropLast_eq_dropLastTR : @dropLast = @dropLastTR := by
  funext α l; simp [dropLastTR]

/-! ## Finding elements -/

/-- Tail recursive implementation of `findRev?`. This is only used at runtime. -/
def findRev?TR (p : α → Bool) (l : List α) : Option α := l.reverse.find? p

@[simp, grind =] theorem find?_singleton {a : α} : [a].find? p = if p a then some a else none := by
  simp only [find?]
  split <;> simp_all

@[simp, grind =] theorem find?_append {xs ys : List α} : (xs ++ ys).find? p = (xs.find? p).or (ys.find? p) := by
  induction xs with
  | nil => simp [find?]
  | cons x xs ih =>
    simp only [cons_append, find?_cons, ih]
    split <;> simp

@[csimp] theorem findRev?_eq_findRev?TR : @List.findRev? = @List.findRev?TR := by
  apply funext; intro α; apply funext; intro p; apply funext; intro l
  induction l with
  | nil => simp [findRev?, findRev?TR]
  | cons x l ih =>
    simp only [findRev?, ih, findRev?TR, reverse_cons, find?_append, find?_singleton]
    split <;> simp_all

@[simp] theorem findRev?_eq_find?_reverse {l : List α} {p : α → Bool} :
    l.findRev? p = l.reverse.find? p := by
  simp [findRev?_eq_findRev?TR, findRev?TR]

/-- Tail recursive implementation of `finSomedRev?`. This is only used at runtime. -/
def findSomeRev?TR (f : α → Option β) (l : List α) : Option β := l.reverse.findSome? f

@[simp, grind =] theorem findSome?_singleton {a : α} :
    [a].findSome? f = f a := by
  simp only [findSome?_cons, findSome?_nil]
  split <;> simp_all

@[simp, grind =] theorem findSome?_append {xs ys : List α} : (xs ++ ys).findSome? f = (xs.findSome? f).or (ys.findSome? f) := by
  induction xs with
  | nil => simp [findSome?]
  | cons x xs ih =>
    simp only [cons_append, findSome?_cons, ih]
    split <;> simp

@[csimp] theorem findSomeRev?_eq_findSomeRev?TR : @List.findSomeRev? = @List.findSomeRev?TR := by
  apply funext; intro α; apply funext; intro β; apply funext; intro p; apply funext; intro l
  induction l with
  | nil => simp [findSomeRev?, findSomeRev?TR]
  | cons x l ih =>
    simp only [findSomeRev?, ih, findSomeRev?TR, reverse_cons, findSome?_append,
      findSome?_singleton]
    split <;> simp_all

@[simp] theorem findSomeRev?_eq_findSome?_reverse {l : List α} {f : α → Option β} :
    l.findSomeRev? f = l.reverse.findSome? f := by
  simp [findSomeRev?_eq_findSomeRev?TR, findSomeRev?TR]

/-! ## Manipulating elements -/

/-! ### replace -/

/--
Replaces the first element of the list `l` that is equal to `a` with `b`. If no element is equal to
`a`, then the list is returned unchanged.

`O(|l|)`. This is a tail-recursive version of `List.replace` that's used in runtime code.

Examples:
* `[1, 4, 2, 3, 3, 7].replaceTR 3 6 = [1, 4, 2, 6, 3, 7]`
* `[1, 4, 2, 3, 3, 7].replaceTR 5 6 = [1, 4, 2, 3, 3, 7]`
-/
@[inline] def replaceTR [BEq α] (l : List α) (b c : α) : List α := go l #[] where
  /-- Auxiliary for `replace`: `replace.go l b c xs acc = acc.toList ++ replace xs b c`,
  unless `b` is not found in `xs` in which case it returns `l`. -/
  @[specialize] go : List α → Array α → List α
  | [], _ => l
  | a::as, acc => bif b == a then acc.toListAppend (c::as) else go as (acc.push a)

@[csimp] theorem replace_eq_replaceTR : @List.replace = @replaceTR := by
  funext α _ l b c; simp [replaceTR]
  suffices ∀ xs acc, l = acc.toList ++ xs →
      replaceTR.go l b c xs acc = acc.toList ++ xs.replace b c from
    (this l #[] (by simp)).symm
  intro xs; induction xs with intro acc
  | nil => simp [replace, replaceTR.go]
  | cons x xs IH =>
    simp only [replaceTR.go, Array.toListAppend_eq, replace]
    split
    · simp [*]
    · intro h; rw [IH] <;> simp_all

/-! ### modify -/

/--
Replaces the element at the given index, if it exists, with the result of applying `f` to it.

This is a tail-recursive version of `List.modify`.

Examples:
 * `[1, 2, 3].modifyTR 0 (· * 10) = [10, 2, 3]`
 * `[1, 2, 3].modifyTR 2 (· * 10) = [1, 2, 30]`
 * `[1, 2, 3].modifyTR 3 (· * 10) = [1, 2, 3]`
-/
def modifyTR (l : List α) (i : Nat) (f : α → α) : List α := go l i #[] where
  /-- Auxiliary for `modifyTR`: `modifyTR.go f l i acc = acc.toList ++ modify f i l`. -/
  go : List α → Nat → Array α → List α
  | [], _, acc => acc.toList
  | a :: l, 0, acc => acc.toListAppend (f a :: l)
  | a :: l, i+1, acc => go l i (acc.push a)

theorem modifyTR_go_eq : ∀ l i, modifyTR.go f l i acc = acc.toList ++ modify l i f
  | [], i => by cases i <;> simp [modifyTR.go, modify]
  | a :: l, 0 => by simp [modifyTR.go, modify]
  | a :: l, i+1 => by simp [modifyTR.go, modify, modifyTR_go_eq l]

@[csimp] theorem modify_eq_modifyTR : @modify = @modifyTR := by
  funext α l i f; simp [modifyTR, modifyTR_go_eq]

/-! ### insertIdx -/

/--
Inserts an element into a list at the specified index. If the index is greater than the length of
the list, then the list is returned unmodified.

In other words, the new element is inserted into the list `l` after the first `i` elements of `l`.

This is a tail-recursive version of `List.insertIdx`, used at runtime.

Examples:
 * `["tues", "thur", "sat"].insertIdxTR 1 "wed" = ["tues", "wed", "thur", "sat"]`
 * `["tues", "thur", "sat"].insertIdxTR 2 "wed" = ["tues", "thur", "wed", "sat"]`
 * `["tues", "thur", "sat"].insertIdxTR 3 "wed" = ["tues", "thur", "sat", "wed"]`
 * `["tues", "thur", "sat"].insertIdxTR 4 "wed" = ["tues", "thur", "sat"]`

-/
@[inline] def insertIdxTR (l : List α) (n : Nat) (a : α) : List α := go n l #[] where
  /-- Auxiliary for `insertIdxTR`: `insertIdxTR.go a n l acc = acc.toList ++ insertIdx n a l`. -/
  go : Nat → List α → Array α → List α
  | 0, l, acc => acc.toListAppend (a :: l)
  | _, [], acc => acc.toList
  | n+1, a :: l, acc => go n l (acc.push a)

theorem insertIdxTR_go_eq : ∀ i l, insertIdxTR.go a i l acc = acc.toList ++ insertIdx l i a
  | 0, l | _+1, [] => by simp [insertIdxTR.go, insertIdx]
  | n+1, a :: l => by simp [insertIdxTR.go, insertIdx, insertIdxTR_go_eq n l]

@[csimp] theorem insertIdx_eq_insertIdxTR : @insertIdx = @insertIdxTR := by
  funext α l i a; simp [insertIdxTR, insertIdxTR_go_eq]

/-! ### erase -/

/--
Removes the first occurrence of `a` from `l`. If `a` does not occur in `l`, the list is returned
unmodified.

`O(|l|)`.

This is a tail-recursive version of `List.erase`, used in runtime code.

Examples:
* `[1, 5, 3, 2, 5].eraseTR 5 = [1, 3, 2, 5]`
* `[1, 5, 3, 2, 5].eraseTR 6 = [1, 5, 3, 2, 5]`
-/
@[inline] def eraseTR [BEq α] (l : List α) (a : α) : List α := go l #[] where
  /-- Auxiliary for `eraseTR`: `eraseTR.go l a xs acc = acc.toList ++ erase xs a`,
  unless `a` is not present in which case it returns `l` -/
  go : List α → Array α → List α
  | [], _ => l
  | x::xs, acc => bif x == a then acc.toListAppend xs else go xs (acc.push x)

@[csimp] theorem erase_eq_eraseTR : @List.erase = @eraseTR := by
  funext α _ l a; simp [eraseTR]
  suffices ∀ xs acc, l = acc.toList ++ xs → eraseTR.go l a xs acc = acc.toList ++ xs.erase a from
    (this l #[] (by simp)).symm
  intro xs; induction xs with intro acc h
  | nil => simp [List.erase, eraseTR.go, h]
  | cons x xs IH =>
    simp only [eraseTR.go, Array.toListAppend_eq, List.erase]
    cases x == a
    · rw [IH] <;> simp_all
    · simp

/--
Removes the first element of a list for which `p` returns `true`. If no element satisfies `p`, then
the list is returned unchanged.

This is a tail-recursive version of `eraseP`, used at runtime.

Examples:
  * `[2, 1, 2, 1, 3, 4].erasePTR (· < 2) = [2, 2, 1, 3, 4]`
  * `[2, 1, 2, 1, 3, 4].erasePTR (· > 2) = [2, 1, 2, 1, 4]`
  * `[2, 1, 2, 1, 3, 4].erasePTR (· > 8) = [2, 1, 2, 1, 3, 4]`
-/
@[inline] def erasePTR (p : α → Bool) (l : List α) : List α := go l #[] where
  /-- Auxiliary for `erasePTR`: `erasePTR.go p l xs acc = acc.toList ++ eraseP p xs`,
  unless `xs` does not contain any elements satisfying `p`, where it returns `l`. -/
  @[specialize] go : List α → Array α → List α
  | [], _ => l
  | a :: l, acc => bif p a then acc.toListAppend l else go l (acc.push a)

@[csimp] theorem eraseP_eq_erasePTR : @eraseP = @erasePTR := by
  funext α p l; simp [erasePTR]
  let rec go (acc) : ∀ xs, l = acc.toList ++ xs →
    erasePTR.go p l xs acc = acc.toList ++ xs.eraseP p
  | [] => fun h => by simp [erasePTR.go, eraseP, h]
  | x::xs => by
    simp [erasePTR.go, eraseP]; cases p x <;> simp
    · intro h; rw [go _ xs]; {simp}; simp [h]
  exact (go #[] _ rfl).symm

/-! ### eraseIdx -/


/--
Removes the element at the specified index. If the index is out of bounds, the list is returned
unmodified.

`O(i)`.

This is a tail-recursive version of `List.eraseIdx`, used at runtime.

Examples:
* `[0, 1, 2, 3, 4].eraseIdxTR 0 = [1, 2, 3, 4]`
* `[0, 1, 2, 3, 4].eraseIdxTR 1 = [0, 2, 3, 4]`
* `[0, 1, 2, 3, 4].eraseIdxTR 5 = [0, 1, 2, 3, 4]`
-/
@[inline] def eraseIdxTR (l : List α) (n : Nat) : List α := go l n #[] where
  /-- Auxiliary for `eraseIdxTR`: `eraseIdxTR.go l n xs acc = acc.toList ++ eraseIdx xs a`,
  unless `a` is not present in which case it returns `l` -/
  go : List α → Nat → Array α → List α
  | [], _, _ => l
  | _::as, 0, acc => acc.toListAppend as
  | a::as, n+1, acc => go as n (acc.push a)

@[csimp] theorem eraseIdx_eq_eraseIdxTR : @eraseIdx = @eraseIdxTR := by
  funext α l i; simp [eraseIdxTR]
  suffices ∀ xs acc, l = acc.toList ++ xs → eraseIdxTR.go l xs i acc = acc.toList ++ xs.eraseIdx i from
    (this l #[] (by simp)).symm
  intro xs; induction xs generalizing i with intro acc h
  | nil => simp [eraseIdx, eraseIdxTR.go, h]
  | cons x xs IH =>
    match i with
    | 0 => simp [eraseIdx, eraseIdxTR.go]
    | i+1 =>
      simp only [eraseIdxTR.go, eraseIdx]
      rw [IH]; simp; simp; exact h

/-! ## Zippers -/

/-! ### zipWith -/

/--
Applies a function to the corresponding elements of two lists, stopping at the end of the shorter
list.

`O(min |xs| |ys|)`. This is a tail-recursive version of `List.zipWith` that's used at runtime.

Examples:
* `[1, 2].zipWithTR (· + ·) [5, 6] = [6, 8]`
* `[1, 2, 3].zipWithTR (· + ·) [5, 6, 10] = [6, 8, 13]`
* `[].zipWithTR (· + ·) [5, 6] = []`
* `[x₁, x₂, x₃].zipWithTR f [y₁, y₂, y₃, y₄] = [f x₁ y₁, f x₂ y₂, f x₃ y₃]`
-/
@[inline] def zipWithTR (f : α → β → γ) (as : List α) (bs : List β) : List γ := go as bs #[] where
  /-- Auxiliary for `zipWith`: `zipWith.go f as bs acc = acc.toList ++ zipWith f as bs` -/
  go : List α → List β → Array γ → List γ
  | a::as, b::bs, acc => go as bs (acc.push (f a b))
  | _, _, acc => acc.toList

@[csimp] theorem zipWith_eq_zipWithTR : @zipWith = @zipWithTR := by
  funext α β γ f as bs
  let rec go : ∀ as bs acc, zipWithTR.go f as bs acc = acc.toList ++ as.zipWith f bs
    | [], _, acc | _::_, [], acc => by simp [zipWithTR.go, zipWith]
    | a::as, b::bs, acc => by simp [zipWithTR.go, zipWith, go as bs]
  exact (go as bs #[]).symm

/-! ## Ranges and enumeration -/

/-! ### zipIdx -/


/--
Pairs each element of a list with its index, optionally starting from an index other than `0`.

`O(|l|)`. This is a tail-recursive version of `List.zipIdx` that's used at runtime.

Examples:
* `[a, b, c].zipIdxTR = [(a, 0), (b, 1), (c, 2)]`
* `[a, b, c].zipIdxTR 5 = [(a, 5), (b, 6), (c, 7)]`
-/
def zipIdxTR (l : List α) (n : Nat := 0) : List (α × Nat) :=
  let as := l.toArray
  (as.foldr (fun a (n, acc) => (n-1, (a, n-1) :: acc)) (n + as.size, [])).2

@[csimp] theorem zipIdx_eq_zipIdxTR : @zipIdx = @zipIdxTR := by
  funext α l n; simp only [zipIdxTR]
  let f := fun (a : α) (n, acc) => (n-1, (a, n-1) :: acc)
  let rec go : ∀ l i, l.foldr f (i + l.length, []) = (i, zipIdx l i)
    | [], n => rfl
    | a::as, n => by
      rw [← show _ + as.length = n + (a::as).length from Nat.succ_add .., foldr, go as]
      simp [zipIdx, f]
  rw [← Array.foldr_toList]
  simp +zetaDelta [go]

/-! ### enumFrom -/

/-- Tail recursive version of `List.enumFrom`. -/
@[deprecated zipIdxTR (since := "2025-01-21")]
def enumFromTR (n : Nat) (l : List α) : List (Nat × α) :=
  let as := l.toArray
  (as.foldr (fun a (n, acc) => (n-1, (n-1, a) :: acc)) (n + as.size, [])).2

set_option linter.deprecated false in
@[deprecated zipIdx_eq_zipIdxTR (since := "2025-01-21"), csimp]
theorem enumFrom_eq_enumFromTR : @enumFrom = @enumFromTR := by
  funext α n l; simp only [enumFromTR]
  let f := fun (a : α) (n, acc) => (n-1, (n-1, a) :: acc)
  let rec go : ∀ l n, l.foldr f (n + l.length, []) = (n, enumFrom n l)
    | [], n => rfl
    | a::as, n => by
      rw [← show _ + as.length = n + (a::as).length from Nat.succ_add .., foldr, go as]
      simp [enumFrom, f]
  rw [← Array.foldr_toList]
  simp +zetaDelta [go]

/-! ## Other list operations -/

/-! ### intercalate -/

set_option linter.listVariables false in
/--
Alternates the lists in `xs` with the separator `sep`.

This is a tail-recursive version of `List.intercalate` used at runtime.

Examples:
* `List.intercalateTR sep [] = []`
* `List.intercalateTR sep [a] = a`
* `List.intercalateTR sep [a, b] = a ++ sep ++ b`
* `List.intercalateTR sep [a, b, c] = a ++ sep ++ b ++ sep ++ c`
-/
def intercalateTR (sep : List α) : (xs : List (List α)) → List α
  | [] => []
  | [x] => x
  | x::xs => go sep.toArray x xs #[]
where
  /-- Auxiliary for `intercalateTR`:
  `intercalateTR.go sep x xs acc = acc.toList ++ intercalate sep.toList (x::xs)` -/
  go (sep : Array α) : List α → List (List α) → Array α → List α
  | x, [], acc => acc.toListAppend x
  | x, y::xs, acc => go sep y xs (acc ++ x ++ sep)

set_option linter.listVariables false in
@[csimp] theorem intercalate_eq_intercalateTR : @intercalate = @intercalateTR := by
  funext α sep l; simp [intercalate, intercalateTR]
  match l with
  | [] => rfl
  | [_] => simp
  | x::y::xs =>
    let rec go {acc x} : ∀ xs,
      intercalateTR.go sep.toArray x xs acc = acc.toList ++ flatten (intersperse sep (x::xs))
    | [] => by simp [intercalateTR.go]
    | _::_ => by simp [intercalateTR.go, go]
    simp [intersperse, go]

end List
