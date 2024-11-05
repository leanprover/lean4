/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Bootstrap

/-!
## Tail recursive implementations for `List` definitions.

Many of the proofs require theorems about `Array`,
so these are in a separate file to minimize imports.

If you import `Init.Data.List.Basic` but do not import this file,
then at runtime you will get non-tail recursive versions of the following definitions.
-/

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

/-- Tail recursive version of `List.set`. -/
@[inline] def setTR (l : List α) (n : Nat) (a : α) : List α := go l n #[] where
  /-- Auxiliary for `setTR`: `setTR.go l a xs n acc = acc.toList ++ set xs a`,
  unless `n ≥ l.length` in which case it returns `l` -/
  go : List α → Nat → Array α → List α
  | [], _, _ => l
  | _::xs, 0, acc => acc.toListAppend (a::xs)
  | x::xs, n+1, acc => go xs n (acc.push x)

@[csimp] theorem set_eq_setTR : @set = @setTR := by
  funext α l n a; simp [setTR]
  let rec go (acc) : ∀ xs n, l = acc.toList ++ xs →
    setTR.go l a xs n acc = acc.toList ++ xs.set n a
  | [], _ => fun h => by simp [setTR.go, set, h]
  | x::xs, 0 => by simp [setTR.go, set]
  | x::xs, n+1 => fun h => by simp only [setTR.go, set]; rw [go _ xs] <;> simp [h]
  exact (go #[] _ _ rfl).symm

/-! ### filterMap -/

/-- Tail recursive version of `filterMap`. -/
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
      simp only [filterMapTR.go, go as, Array.push_toList, append_assoc, singleton_append,
        filterMap]
      split <;> simp [*]
  exact (go l #[]).symm

/-! ### foldr -/

/-- Tail recursive version of `List.foldr`. -/
@[specialize] def foldrTR (f : α → β → β) (init : β) (l : List α) : β := l.toArray.foldr f init

@[csimp] theorem foldr_eq_foldrTR : @foldr = @foldrTR := by
  funext α β f init l; simp [foldrTR, Array.foldr_eq_foldr_toList, -Array.size_toArray]

/-! ### flatMap  -/

/-- Tail recursive version of `List.flatMap`. -/
@[inline] def flatMapTR (as : List α) (f : α → List β) : List β := go as #[] where
  /-- Auxiliary for `flatMap`: `flatMap.go f as = acc.toList ++ bind f as` -/
  @[specialize] go : List α → Array β → List β
  | [], acc => acc.toList
  | x::xs, acc => go xs (acc ++ f x)

@[csimp] theorem flatMap_eq_flatMapTR : @List.flatMap = @flatMapTR := by
  funext α β as f
  let rec go : ∀ as acc, flatMapTR.go f as acc = acc.toList ++ as.flatMap f
    | [], acc => by simp [flatMapTR.go, flatMap]
    | x::xs, acc => by simp [flatMapTR.go, flatMap, go xs]
  exact (go as #[]).symm

/-! ### flatten -/

/-- Tail recursive version of `List.flatten`. -/
@[inline] def flattenTR (l : List (List α)) : List α := flatMapTR l id

@[csimp] theorem flatten_eq_flattenTR : @flatten = @flattenTR := by
  funext α l; rw [← List.flatMap_id, List.flatMap_eq_flatMapTR]; rfl

/-! ## Sublists -/

/-! ### take -/

/-- Tail recursive version of `List.take`. -/
@[inline] def takeTR (n : Nat) (l : List α) : List α := go l n #[] where
  /-- Auxiliary for `take`: `take.go l xs n acc = acc.toList ++ take n xs`,
  unless `n ≥ xs.length` in which case it returns `l`. -/
  @[specialize] go : List α → Nat → Array α → List α
  | [], _, _ => l
  | _::_, 0, acc => acc.toList
  | a::as, n+1, acc => go as n (acc.push a)

@[csimp] theorem take_eq_takeTR : @take = @takeTR := by
  funext α n l; simp [takeTR]
  suffices ∀ xs acc, l = acc.toList ++ xs → takeTR.go l xs n acc = acc.toList ++ xs.take n from
    (this l #[] (by simp)).symm
  intro xs; induction xs generalizing n with intro acc
  | nil => cases n <;> simp [take, takeTR.go]
  | cons x xs IH =>
    cases n with simp only [take, takeTR.go]
    | zero => simp
    | succ n => intro h; rw [IH] <;> simp_all

/-! ### takeWhile -/

/-- Tail recursive version of `List.takeWhile`. -/
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

/-- Tail recursive version of `dropLast`. -/
@[inline] def dropLastTR (l : List α) : List α := l.toArray.pop.toList

@[csimp] theorem dropLast_eq_dropLastTR : @dropLast = @dropLastTR := by
  funext α l; simp [dropLastTR]

/-! ## Manipulating elements -/

/-! ### replace -/

/-- Tail recursive version of `List.replace`. -/
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

/-- Tail-recursive version of `modify`. -/
def modifyTR (f : α → α) (n : Nat) (l : List α) : List α := go l n #[] where
  /-- Auxiliary for `modifyTR`: `modifyTR.go f l n acc = acc.toList ++ modify f n l`. -/
  go : List α → Nat → Array α → List α
  | [], _, acc => acc.toList
  | a :: l, 0, acc => acc.toListAppend (f a :: l)
  | a :: l, n+1, acc => go l n (acc.push a)

theorem modifyTR_go_eq : ∀ l n, modifyTR.go f l n acc = acc.toList ++ modify f n l
  | [], n => by cases n <;> simp [modifyTR.go, modify]
  | a :: l, 0 => by simp [modifyTR.go, modify]
  | a :: l, n+1 => by simp [modifyTR.go, modify, modifyTR_go_eq l]

@[csimp] theorem modify_eq_modifyTR : @modify = @modifyTR := by
  funext α f n l; simp [modifyTR, modifyTR_go_eq]

/-! ### insertIdx -/

/-- Tail-recursive version of `insertIdx`. -/
@[inline] def insertIdxTR (n : Nat) (a : α) (l : List α) : List α := go n l #[] where
  /-- Auxiliary for `insertIdxTR`: `insertIdxTR.go a n l acc = acc.toList ++ insertIdx n a l`. -/
  go : Nat → List α → Array α → List α
  | 0, l, acc => acc.toListAppend (a :: l)
  | _, [], acc => acc.toList
  | n+1, a :: l, acc => go n l (acc.push a)

theorem insertIdxTR_go_eq : ∀ n l, insertIdxTR.go a n l acc = acc.toList ++ insertIdx n a l
  | 0, l | _+1, [] => by simp [insertIdxTR.go, insertIdx]
  | n+1, a :: l => by simp [insertIdxTR.go, insertIdx, insertIdxTR_go_eq n l]

@[csimp] theorem insertIdx_eq_insertIdxTR : @insertIdx = @insertIdxTR := by
  funext α f n l; simp [insertIdxTR, insertIdxTR_go_eq]

/-! ### erase -/

/-- Tail recursive version of `List.erase`. -/
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

/-- Tail-recursive version of `eraseP`. -/
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

/-- Tail recursive version of `List.eraseIdx`. -/
@[inline] def eraseIdxTR (l : List α) (n : Nat) : List α := go l n #[] where
  /-- Auxiliary for `eraseIdxTR`: `eraseIdxTR.go l n xs acc = acc.toList ++ eraseIdx xs a`,
  unless `a` is not present in which case it returns `l` -/
  go : List α → Nat → Array α → List α
  | [], _, _ => l
  | _::as, 0, acc => acc.toListAppend as
  | a::as, n+1, acc => go as n (acc.push a)

@[csimp] theorem eraseIdx_eq_eraseIdxTR : @eraseIdx = @eraseIdxTR := by
  funext α l n; simp [eraseIdxTR]
  suffices ∀ xs acc, l = acc.toList ++ xs → eraseIdxTR.go l xs n acc = acc.toList ++ xs.eraseIdx n from
    (this l #[] (by simp)).symm
  intro xs; induction xs generalizing n with intro acc h
  | nil => simp [eraseIdx, eraseIdxTR.go, h]
  | cons x xs IH =>
    match n with
    | 0 => simp [eraseIdx, eraseIdxTR.go]
    | n+1 =>
      simp only [eraseIdxTR.go, eraseIdx]
      rw [IH]; simp; simp; exact h

/-! ## Zippers -/

/-! ### zipWith -/

/-- Tail recursive version of `List.zipWith`. -/
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

/-! ### enumFrom -/

/-- Tail recursive version of `List.enumFrom`. -/
def enumFromTR (n : Nat) (l : List α) : List (Nat × α) :=
  let arr := l.toArray
  (arr.foldr (fun a (n, acc) => (n-1, (n-1, a) :: acc)) (n + arr.size, [])).2

@[csimp] theorem enumFrom_eq_enumFromTR : @enumFrom = @enumFromTR := by
  funext α n l; simp [enumFromTR, -Array.size_toArray]
  let f := fun (a : α) (n, acc) => (n-1, (n-1, a) :: acc)
  let rec go : ∀ l n, l.foldr f (n + l.length, []) = (n, enumFrom n l)
    | [], n => rfl
    | a::as, n => by
      rw [← show _ + as.length = n + (a::as).length from Nat.succ_add .., foldr, go as]
      simp [enumFrom, f]
  rw [Array.foldr_eq_foldr_toList]
  simp [go]

/-! ## Other list operations -/

/-! ### intercalate -/

/-- Tail recursive version of `List.intercalate`. -/
def intercalateTR (sep : List α) : List (List α) → List α
  | [] => []
  | [x] => x
  | x::xs => go sep.toArray x xs #[]
where
  /-- Auxiliary for `intercalateTR`:
  `intercalateTR.go sep x xs acc = acc.toList ++ intercalate sep.toList (x::xs)` -/
  go (sep : Array α) : List α → List (List α) → Array α → List α
  | x, [], acc => acc.toListAppend x
  | x, y::xs, acc => go sep y xs (acc ++ x ++ sep)

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
