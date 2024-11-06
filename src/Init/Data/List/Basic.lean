/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation

/-!
# Basic operations on `List`.

We define
* basic operations on `List`,
* simp lemmas for applying the operations on `.nil` and `.cons` arguments
  (in the cases where the right hand side is simple to state; otherwise these are deferred to `Init.Data.List.Lemmas`),
* the minimal lemmas which are required for setting up `Init.Data.Array.Basic`.

In `Init.Data.List.Impl` we give tail-recursive versions of these operations
along with `@[csimp]` lemmas,

In `Init.Data.List.Lemmas` we develop the full API for these functions.

Recall that `length`, `get`, `set`, `foldl`, and `concat` have already been defined in `Init.Prelude`.

The operations are organized as follow:
* Equality: `beq`, `isEqv`.
* Lexicographic ordering: `lt`, `le`, and instances.
* Head and tail operators: `head`, `head?`, `headD?`, `tail`, `tail?`, `tailD`.
* Basic operations:
  `map`, `filter`, `filterMap`, `foldr`, `append`, `flatten`, `pure`, `flatMap`, `replicate`, and
  `reverse`.
* Additional functions defined in terms of these: `leftpad`, `rightPad`, and `reduceOption`.
* Operations using indexes: `mapIdx`.
* List membership: `isEmpty`, `elem`, `contains`, `mem` (and the `∈` notation),
  and decidability for predicates quantifying over membership in a `List`.
* Sublists: `take`, `drop`, `takeWhile`, `dropWhile`, `partition`, `dropLast`,
  `isPrefixOf`, `isPrefixOf?`, `isSuffixOf`, `isSuffixOf?`, `Subset`, `Sublist`,
  `rotateLeft` and `rotateRight`.
* Manipulating elements: `replace`, `modify`, `insert`, `insertIdx`, `erase`, `eraseP`, `eraseIdx`.
* Finding elements: `find?`, `findSome?`, `findIdx`, `indexOf`, `findIdx?`, `indexOf?`,
 `countP`, `count`, and `lookup`.
* Logic: `any`, `all`, `or`, and `and`.
* Zippers: `zipWith`, `zip`, `zipWithAll`, and `unzip`.
* Ranges and enumeration: `range`, `iota`, `enumFrom`, and `enum`.
* Minima and maxima: `min?` and `max?`.
* Other functions: `intersperse`, `intercalate`, `eraseDups`, `eraseReps`, `span`, `splitBy`,
  `removeAll`
  (currently these functions are mostly only used in meta code,
  and do not have API suitable for verification).

Further operations are defined in `Init.Data.List.BasicAux`
(because they use `Array` in their implementations), namely:
* Variant getters: `get!`, `get?`, `getD`, `getLast`, `getLast!`, `getLast?`, and `getLastD`.
* Head and tail: `head!`, `tail!`.
* Other operations on sublists: `partitionMap`, `rotateLeft`, and `rotateRight`.
-/

set_option linter.missingDocs true -- keep it documented

open Decidable List

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

/-! ## Preliminaries from `Init.Prelude` -/

/-! ### length -/

@[simp] theorem length_nil : length ([] : List α) = 0 :=
  rfl

@[simp 1100] theorem length_singleton (a : α) : length [a] = 1 := rfl

@[simp] theorem length_cons {α} (a : α) (as : List α) : (cons a as).length = as.length + 1 :=
  rfl

/-! ### set -/

@[simp] theorem length_set (as : List α) (i : Nat) (a : α) : (as.set i a).length = as.length := by
  induction as generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [set, ih]

/-! ### foldl -/

-- As `List.foldl` is defined in `Init.Prelude`, we write the basic simplification lemmas here.
@[simp] theorem foldl_nil : [].foldl f b = b := rfl
@[simp] theorem foldl_cons (l : List α) (b : β) : (a :: l).foldl f b = l.foldl f (f b a) := rfl

/-! ### concat -/

theorem length_concat (as : List α) (a : α) : (concat as a).length = as.length + 1 := by
  induction as with
  | nil => rfl
  | cons _ xs ih => simp [concat, ih]

theorem of_concat_eq_concat {as bs : List α} {a b : α} (h : as.concat a = bs.concat b) : as = bs ∧ a = b := by
  match as, bs with
  | [], [] => simp [concat] at h; simp [h]
  | [_], [] => simp [concat] at h
  | _::_::_, [] => simp [concat] at h
  | [], [_] => simp [concat] at h
  | [], _::_::_ => simp [concat] at h
  | _::_, _::_ => simp [concat] at h; simp [h]; apply of_concat_eq_concat h.2

/-! ## Equality -/

/--
The equality relation on lists asserts that they have the same length
and they are pairwise `BEq`.
-/
protected def beq [BEq α] : List α → List α → Bool
  | [],    []    => true
  | a::as, b::bs => a == b && List.beq as bs
  | _,     _     => false

@[simp] theorem beq_nil_nil [BEq α] : List.beq ([] : List α) ([] : List α) = true := rfl
@[simp] theorem beq_cons_nil [BEq α] (a : α) (as : List α) : List.beq (a::as) [] = false := rfl
@[simp] theorem beq_nil_cons [BEq α] (a : α) (as : List α) : List.beq [] (a::as) = false := rfl
theorem beq_cons₂ [BEq α] (a b : α) (as bs : List α) : List.beq (a::as) (b::bs) = (a == b && List.beq as bs) := rfl

instance [BEq α] : BEq (List α) := ⟨List.beq⟩

instance [BEq α] [LawfulBEq α] : LawfulBEq (List α) where
  eq_of_beq {as bs} := by
    induction as generalizing bs with
    | nil => intro h; cases bs <;> first | rfl | contradiction
    | cons a as ih =>
      cases bs with
      | nil => intro h; contradiction
      | cons b bs =>
        simp [show (a::as == b::bs) = (a == b && as == bs) from rfl, -and_imp]
        intro ⟨h₁, h₂⟩
        exact ⟨h₁, ih h₂⟩
  rfl {as} := by
    induction as with
    | nil => rfl
    | cons a as ih => simp [BEq.beq, List.beq, LawfulBEq.rfl]; exact ih

/--
`O(min |as| |bs|)`. Returns true if `as` and `bs` have the same length,
and they are pairwise related by `eqv`.
-/
@[specialize] def isEqv : (as bs : List α) → (eqv : α → α → Bool) → Bool
  | [],    [],    _   => true
  | a::as, b::bs, eqv => eqv a b && isEqv as bs eqv
  | _,     _,     _   => false

@[simp] theorem isEqv_nil_nil : isEqv ([] : List α) [] eqv = true := rfl
@[simp] theorem isEqv_nil_cons : isEqv ([] : List α) (a::as) eqv = false := rfl
@[simp] theorem isEqv_cons_nil : isEqv (a::as : List α) [] eqv = false := rfl
theorem isEqv_cons₂ : isEqv (a::as) (b::bs) eqv = (eqv a b && isEqv as bs eqv) := rfl


/-! ## Lexicographic ordering -/

/--
The lexicographic order on lists.
`[] < a::as`, and `a::as < b::bs` if `a < b` or if `a` and `b` are equivalent and `as < bs`.
-/
inductive lt [LT α] : List α → List α → Prop where
  /-- `[]` is the smallest element in the order. -/
  | nil  (b : α) (bs : List α) : lt [] (b::bs)
  /-- If `a < b` then `a::as < b::bs`. -/
  | head {a : α} (as : List α) {b : α} (bs : List α) : a < b → lt (a::as) (b::bs)
  /-- If `a` and `b` are equivalent and `as < bs`, then `a::as < b::bs`. -/
  | tail {a : α} {as : List α} {b : α} {bs : List α} : ¬ a < b → ¬ b < a → lt as bs → lt (a::as) (b::bs)

instance [LT α] : LT (List α) := ⟨List.lt⟩

instance hasDecidableLt [LT α] [h : DecidableRel (α := α) (· < ·)] : (l₁ l₂ : List α) → Decidable (l₁ < l₂)
  | [],    []    => isFalse nofun
  | [],    _::_  => isTrue (List.lt.nil _ _)
  | _::_, []     => isFalse nofun
  | a::as, b::bs =>
    match h a b with
    | isTrue h₁  => isTrue (List.lt.head _ _ h₁)
    | isFalse h₁ =>
      match h b a with
      | isTrue h₂  => isFalse (fun h => match h with
         | List.lt.head _ _ h₁' => absurd h₁' h₁
         | List.lt.tail _ h₂' _ => absurd h₂ h₂')
      | isFalse h₂ =>
        match hasDecidableLt as bs with
        | isTrue h₃  => isTrue (List.lt.tail h₁ h₂ h₃)
        | isFalse h₃ => isFalse (fun h => match h with
           | List.lt.head _ _ h₁' => absurd h₁' h₁
           | List.lt.tail _ _ h₃' => absurd h₃' h₃)

/-- The lexicographic order on lists. -/
@[reducible] protected def le [LT α] (a b : List α) : Prop := ¬ b < a

instance [LT α] : LE (List α) := ⟨List.le⟩

instance [LT α] [DecidableRel ((· < ·) : α → α → Prop)] : (l₁ l₂ : List α) → Decidable (l₁ ≤ l₂) :=
  fun _ _ => inferInstanceAs (Decidable (Not _))

/-! ## Alternative getters -/

/-! ### get? -/

/--
Returns the `i`-th element in the list (zero-based).

If the index is out of bounds (`i ≥ as.length`), this function returns `none`.
Also see `get`, `getD` and `get!`.
-/
def get? : (as : List α) → (i : Nat) → Option α
  | a::_,  0   => some a
  | _::as, n+1 => get? as n
  | _,     _   => none

@[simp] theorem get?_nil : @get? α [] n = none := rfl
@[simp] theorem get?_cons_zero : @get? α (a::l) 0 = some a := rfl
@[simp] theorem get?_cons_succ : @get? α (a::l) (n+1) = get? l n := rfl

theorem ext_get? : ∀ {l₁ l₂ : List α}, (∀ n, l₁.get? n = l₂.get? n) → l₁ = l₂
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h 0
  | [], _ :: _, h => nomatch h 0
  | a :: l₁, a' :: l₂, h => by
    have h0 : some a = some a' := h 0
    injection h0 with aa; simp only [aa, ext_get? fun n => h (n+1)]

/-- Deprecated alias for `ext_get?`. The preferred extensionality theorem is now `ext_getElem?`. -/
@[deprecated (since := "2024-06-07")] abbrev ext := @ext_get?

/-! ### getD -/

/--
Returns the `i`-th element in the list (zero-based).

If the index is out of bounds (`i ≥ as.length`), this function returns `fallback`.
See also `get?` and `get!`.
-/
def getD (as : List α) (i : Nat) (fallback : α) : α :=
  (as.get? i).getD fallback

@[simp] theorem getD_nil : getD [] n d = d := rfl
@[simp] theorem getD_cons_zero : getD (x :: xs) 0 d = x := rfl
@[simp] theorem getD_cons_succ : getD (x :: xs) (n + 1) d = getD xs n d := rfl

/-! ### getLast -/

/--
Returns the last element of a non-empty list.
-/
def getLast : ∀ (as : List α), as ≠ [] → α
  | [],       h => absurd rfl h
  | [a],      _ => a
  | _::b::as, _ => getLast (b::as) (fun h => List.noConfusion h)

/-! ### getLast? -/

/--
Returns the last element in the list.

If the list is empty, this function returns `none`.
Also see `getLastD` and `getLast!`.
-/
def getLast? : List α → Option α
  | []    => none
  | a::as => some (getLast (a::as) (fun h => List.noConfusion h))

@[simp] theorem getLast?_nil : @getLast? α [] = none := rfl

/-! ### getLastD -/

/--
Returns the last element in the list.

If the list is empty, this function returns `fallback`.
Also see `getLast?` and `getLast!`.
-/
def getLastD : (as : List α) → (fallback : α) → α
  | [],   a₀ => a₀
  | a::as, _ => getLast (a::as) (fun h => List.noConfusion h)

-- These aren't `simp` lemmas since we always simplify `getLastD` in terms of `getLast?`.
theorem getLastD_nil (a) : @getLastD α [] a = a := rfl
theorem getLastD_cons (a b l) : @getLastD α (b::l) a = getLastD l b := by cases l <;> rfl

/-! ## Head and tail -/

/-! ### head -/

/--
Returns the first element of a non-empty list.
-/
def head : (as : List α) → as ≠ [] → α
  | a::_, _ => a

@[simp] theorem head_cons : @head α (a::l) h = a := rfl

/-! ### head? -/

/--
Returns the first element in the list.

If the list is empty, this function returns `none`.
Also see `headD` and `head!`.
-/
def head? : List α → Option α
  | []   => none
  | a::_ => some a

@[simp] theorem head?_nil : @head? α [] = none := rfl
@[simp] theorem head?_cons : @head? α (a::l) = some a := rfl

/-! ### headD -/

/--
Returns the first element in the list.

If the list is empty, this function returns `fallback`.
Also see `head?` and `head!`.
-/
def headD : (as : List α) → (fallback : α) → α
  | [],   fallback => fallback
  | a::_, _  => a

@[simp 1100] theorem headD_nil : @headD α [] d = d := rfl
@[simp 1100] theorem headD_cons : @headD α (a::l) d = a := rfl

/-! ### tail -/

/-- Get the tail of a nonempty list, or return `[]` for `[]`. -/
def tail : List α → List α
  | []    => []
  | _::as => as

@[simp] theorem tail_nil : @tail α [] = [] := rfl
@[simp] theorem tail_cons : @tail α (a::as) = as := rfl

/-! ### tail? -/

/--
Drops the first element of the list.

If the list is empty, this function returns `none`.
Also see `tailD` and `tail!`.
-/
def tail? : List α → Option (List α)
  | []    => none
  | _::as => some as

@[simp] theorem tail?_nil : @tail? α [] = none := rfl
@[simp] theorem tail?_cons : @tail? α (a::l) = some l := rfl

/-! ### tailD -/

/--
Drops the first element of the list.

If the list is empty, this function returns `fallback`.
Also see `head?` and `head!`.
-/
def tailD (list fallback : List α) : List α :=
  match list with
  | [] => fallback
  | _ :: tl => tl

@[simp 1100] theorem tailD_nil : @tailD α [] l' = l' := rfl
@[simp 1100] theorem tailD_cons : @tailD α (a::l) l' = l := rfl

/-! ## Basic `List` operations.

We define the basic functional programming operations on `List`:
`map`, `filter`, `filterMap`, `foldr`, `append`, `flatten`, `pure`, `bind`, `replicate`, and `reverse`.
-/

/-! ### map -/

/--
`O(|l|)`. `map f l` applies `f` to each element of the list.
* `map f [a, b, c] = [f a, f b, f c]`
-/
@[specialize] def map (f : α → β) : List α → List β
  | []    => []
  | a::as => f a :: map f as

@[simp] theorem map_nil {f : α → β} : map f [] = [] := rfl
@[simp] theorem map_cons (f : α → β) a l : map f (a :: l) = f a :: map f l := rfl

/-! ### filter -/

/--
`O(|l|)`. `filter f l` returns the list of elements in `l` for which `f` returns true.
```
filter (· > 2) [1, 2, 5, 2, 7, 7] = [5, 7, 7]
```
-/
def filter (p : α → Bool) : List α → List α
  | [] => []
  | a::as => match p a with
    | true => a :: filter p as
    | false => filter p as

@[simp] theorem filter_nil (p : α → Bool) : filter p [] = [] := rfl

/-! ### filterMap -/

/--
`O(|l|)`. `filterMap f l` takes a function `f : α → Option β` and applies it to each element of `l`;
the resulting non-`none` values are collected to form the output list.
```
filterMap
  (fun x => if x > 2 then some (2 * x) else none)
  [1, 2, 5, 2, 7, 7]
= [10, 14, 14]
```
-/
@[specialize] def filterMap (f : α → Option β) : List α → List β
  | []   => []
  | a::as =>
    match f a with
    | none   => filterMap f as
    | some b => b :: filterMap f as

@[simp] theorem filterMap_nil (f : α → Option β) : filterMap f [] = [] := rfl
theorem filterMap_cons (f : α → Option β) (a : α) (l : List α) :
    filterMap f (a :: l) =
      match f a with
      | none => filterMap f l
      | some b => b :: filterMap f l := rfl

/-! ### foldr -/

/--
`O(|l|)`. Applies function `f` to all of the elements of the list, from right to left.
* `foldr f init [a, b, c] = f a <| f b <| f c <| init`
-/
@[specialize] def foldr (f : α → β → β) (init : β) : List α → β
  | []     => init
  | a :: l => f a (foldr f init l)

@[simp] theorem foldr_nil : [].foldr f b = b := rfl
@[simp] theorem foldr_cons (l : List α) : (a :: l).foldr f b = f a (l.foldr f b) := rfl

/-! ### reverse -/

/-- Auxiliary for `List.reverse`. `List.reverseAux l r = l.reverse ++ r`, but it is defined directly. -/
def reverseAux : List α → List α → List α
  | [],   r => r
  | a::l, r => reverseAux l (a::r)

@[simp] theorem reverseAux_nil : reverseAux [] r = r := rfl
@[simp] theorem reverseAux_cons : reverseAux (a::l) r = reverseAux l (a::r) := rfl

/--
`O(|as|)`. Reverse of a list:
* `[1, 2, 3, 4].reverse = [4, 3, 2, 1]`

Note that because of the "functional but in place" optimization implemented by Lean's compiler,
this function works without any allocations provided that the input list is unshared:
it simply walks the linked list and reverses all the node pointers.
-/
def reverse (as : List α) : List α :=
  reverseAux as []

@[simp] theorem reverse_nil : reverse ([] : List α) = [] := rfl

theorem reverseAux_reverseAux (as bs cs : List α) : reverseAux (reverseAux as bs) cs = reverseAux bs (reverseAux (reverseAux as []) cs) := by
  induction as generalizing bs cs with
  | nil => rfl
  | cons a as ih => simp [reverseAux, ih (a::bs), ih [a]]

/-! ### append -/

/--
`O(|xs|)`: append two lists. `[1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5]`.
It takes time proportional to the first list.
-/
protected def append : (xs ys : List α) → List α
  | [],    bs => bs
  | a::as, bs => a :: List.append as bs

/-- Tail-recursive version of `List.append`.

Most of the tail-recursive implementations are in `Init.Data.List.Impl`,
but `appendTR` must be set up immediately,
because otherwise `Append (List α)` instance below will not use it.
-/
def appendTR (as bs : List α) : List α :=
  reverseAux as.reverse bs

@[csimp] theorem append_eq_appendTR : @List.append = @appendTR := by
  apply funext; intro α; apply funext; intro as; apply funext; intro bs
  simp [appendTR, reverse]
  induction as with
  | nil  => rfl
  | cons a as ih =>
    rw [reverseAux, reverseAux_reverseAux]
    simp [List.append, ih, reverseAux]

instance : Append (List α) := ⟨List.append⟩

@[simp] theorem append_eq (as bs : List α) : List.append as bs = as ++ bs := rfl

@[simp] theorem nil_append (as : List α) : [] ++ as = as := rfl
@[simp] theorem cons_append (a : α) (as bs : List α) : (a::as) ++ bs = a::(as ++ bs) := rfl

@[simp] theorem append_nil (as : List α) : as ++ [] = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp_all only [HAppend.hAppend, Append.append, List.append]

instance : Std.LawfulIdentity (α := List α) (· ++ ·) [] where
  left_id := nil_append
  right_id := append_nil

@[simp] theorem length_append (as bs : List α) : (as ++ bs).length = as.length + bs.length := by
  induction as with
  | nil => simp
  | cons _ as ih => simp [ih, Nat.succ_add]

@[simp] theorem append_assoc (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

instance : Std.Associative (α := List α) (· ++ ·) := ⟨append_assoc⟩

theorem append_cons (as : List α) (b : α) (bs : List α) : as ++ b :: bs = as ++ [b] ++ bs := by
  simp

@[simp] theorem concat_eq_append (as : List α) (a : α) : as.concat a = as ++ [a] := by
  induction as <;> simp [concat, *]

theorem reverseAux_eq_append (as bs : List α) : reverseAux as bs = reverseAux as [] ++ bs := by
  induction as generalizing bs with
  | nil => simp [reverseAux]
  | cons a as ih =>
    simp [reverseAux]
    rw [ih (a :: bs), ih [a], append_assoc]
    rfl

@[simp] theorem reverse_cons (a : α) (as : List α) : reverse (a :: as) = reverse as ++ [a] := by
  simp [reverse, reverseAux]
  rw [← reverseAux_eq_append]

/-! ### flatten -/

/--
`O(|flatten L|)`. `join L` concatenates all the lists in `L` into one list.
* `flatten [[a], [], [b, c], [d, e, f]] = [a, b, c, d, e, f]`
-/
def flatten : List (List α) → List α
  | []      => []
  | a :: as => a ++ flatten as

@[simp] theorem flatten_nil : List.flatten ([] : List (List α)) = [] := rfl
@[simp] theorem flatten_cons : (l :: ls).flatten = l ++ ls.flatten := rfl

@[deprecated flatten (since := "2024-10-14"), inherit_doc flatten] abbrev join := @flatten

/-! ### singleton -/

/-- `singleton x = [x]`. -/
@[inline] protected def singleton {α : Type u} (a : α) : List α := [a]

set_option linter.missingDocs false in
@[deprecated singleton (since := "2024-10-16")] protected abbrev pure := @singleton

/-! ### flatMap -/

/--
`flatMap xs f` applies `f` to each element of `xs`
to get a list of lists, and then concatenates them all together.
* `[2, 3, 2].bind range = [0, 1, 0, 1, 2, 0, 1]`
-/
@[inline] def flatMap {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β := flatten (map b a)

@[simp] theorem flatMap_nil (f : α → List β) : List.flatMap [] f = [] := by simp [flatten, List.flatMap]
@[simp] theorem flatMap_cons x xs (f : α → List β) :
  List.flatMap (x :: xs) f = f x ++ List.flatMap xs f := by simp [flatten, List.flatMap]

set_option linter.missingDocs false in
@[deprecated flatMap (since := "2024-10-16")] abbrev bind := @flatMap
set_option linter.missingDocs false in
@[deprecated flatMap_nil (since := "2024-10-16")] abbrev nil_flatMap := @flatMap_nil
set_option linter.missingDocs false in
@[deprecated flatMap_cons (since := "2024-10-16")] abbrev cons_flatMap := @flatMap_cons

set_option linter.missingDocs false in
@[deprecated flatMap_nil (since := "2024-06-15")] abbrev nil_bind := @flatMap_nil
set_option linter.missingDocs false in
@[deprecated flatMap_cons (since := "2024-06-15")] abbrev cons_bind := @flatMap_cons

/-! ### replicate -/

/--
`replicate n a` is `n` copies of `a`:
* `replicate 5 a = [a, a, a, a, a]`
-/
def replicate : (n : Nat) → (a : α) → List α
  | 0,   _ => []
  | n+1, a => a :: replicate n a

@[simp] theorem replicate_zero : replicate 0 a = [] := rfl
theorem replicate_succ (a : α) (n) : replicate (n+1) a = a :: replicate n a := rfl

@[simp] theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [ih, replicate_succ, length_cons, Nat.succ_eq_add_one]

/-! ## Additional functions -/

/-! ### leftpad and rightpad -/

/--
Pads `l : List α` on the left with repeated occurrences of `a : α` until it is of length `n`.
If `l` is initially larger than `n`, just return `l`.
-/
def leftpad (n : Nat) (a : α) (l : List α) : List α := replicate (n - length l) a ++ l

/--
Pads `l : List α` on the right with repeated occurrences of `a : α` until it is of length `n`.
If `l` is initially larger than `n`, just return `l`.
-/
def rightpad (n : Nat) (a : α) (l : List α) : List α := l ++ replicate (n - length l) a

/-! ### reduceOption -/

/-- Drop `none`s from a list, and replace each remaining `some a` with `a`. -/
@[inline] def reduceOption {α} : List (Option α) → List α :=
  List.filterMap id

/-! ## List membership

* `L.contains a : Bool` determines, using a `[BEq α]` instance, whether `L` contains an element `· == a`.
* `a ∈ L : Prop` is the proposition (only decidable if `α` has decidable equality) that `L` contains an element `· = a`.
-/

/-! ### EmptyCollection -/

instance : EmptyCollection (List α) := ⟨List.nil⟩

@[simp] theorem empty_eq : (∅ : List α) = [] := rfl

/-! ### isEmpty -/

/--
`O(1)`. `isEmpty l` is true if the list is empty.
* `isEmpty [] = true`
* `isEmpty [a] = false`
* `isEmpty [a, b] = false`
-/
def isEmpty : List α → Bool
  | []     => true
  | _ :: _ => false

@[simp] theorem isEmpty_nil : ([] : List α).isEmpty = true := rfl
@[simp] theorem isEmpty_cons : (x :: xs : List α).isEmpty = false := rfl

/-! ### elem -/

/--
`O(|l|)`. `elem a l` or `l.contains a` is true if there is an element in `l` equal to `a`.

* `elem 3 [1, 4, 2, 3, 3, 7] = true`
* `elem 5 [1, 4, 2, 3, 3, 7] = false`
-/
def elem [BEq α] (a : α) : List α → Bool
  | []    => false
  | b::bs => match a == b with
    | true  => true
    | false => elem a bs

@[simp] theorem elem_nil [BEq α] : ([] : List α).elem a = false := rfl
theorem elem_cons [BEq α] {a : α} :
    (b::bs).elem a = match a == b with | true => true | false => bs.elem a := rfl

/-- `notElem a l` is `!(elem a l)`. -/
@[deprecated (since := "2024-06-15")]
def notElem [BEq α] (a : α) (as : List α) : Bool :=
  !(as.elem a)

/-! ### contains -/

@[inherit_doc elem] abbrev contains [BEq α] (as : List α) (a : α) : Bool :=
  elem a as

@[simp] theorem contains_nil [BEq α] : ([] : List α).contains a = false := rfl

/-! ### Mem -/

/--
`a ∈ l` is a predicate which asserts that `a` is in the list `l`.
Unlike `elem`, this uses `=` instead of `==` and is suited for mathematical reasoning.
* `a ∈ [x, y, z] ↔ a = x ∨ a = y ∨ a = z`
-/
inductive Mem (a : α) : List α → Prop
  /-- The head of a list is a member: `a ∈ a :: as`. -/
  | head (as : List α) : Mem a (a::as)
  /-- A member of the tail of a list is a member of the list: `a ∈ l → a ∈ b :: l`. -/
  | tail (b : α) {as : List α} : Mem a as → Mem a (b::as)

instance : Membership α (List α) where
  mem l a := Mem a l

theorem mem_of_elem_eq_true [BEq α] [LawfulBEq α] {a : α} {as : List α} : elem a as = true → a ∈ as := by
  match as with
  | [] => simp [elem]
  | a'::as =>
    simp [elem]
    split
    next h => intros; simp [BEq.beq] at h; subst h; apply Mem.head
    next _ => intro h; exact Mem.tail _ (mem_of_elem_eq_true h)

theorem elem_eq_true_of_mem [BEq α] [LawfulBEq α] {a : α} {as : List α} (h : a ∈ as) : elem a as = true := by
  induction h with
  | head _ => simp [elem]
  | tail _ _ ih => simp [elem]; split; rfl; assumption

instance [BEq α] [LawfulBEq α] (a : α) (as : List α) : Decidable (a ∈ as) :=
  decidable_of_decidable_of_iff (Iff.intro mem_of_elem_eq_true elem_eq_true_of_mem)

theorem mem_append_of_mem_left {a : α} {as : List α} (bs : List α) : a ∈ as → a ∈ as ++ bs := by
  intro h
  induction h with
  | head => apply Mem.head
  | tail => apply Mem.tail; assumption

theorem mem_append_of_mem_right {b : α} {bs : List α} (as : List α) : b ∈ bs → b ∈ as ++ bs := by
  intro h
  induction as with
  | nil  => simp [h]
  | cons => apply Mem.tail; assumption

instance decidableBEx (p : α → Prop) [DecidablePred p] :
    ∀ l : List α, Decidable (Exists fun x => x ∈ l ∧ p x)
  | [] => isFalse nofun
  | x :: xs =>
    if h₁ : p x then isTrue ⟨x, .head .., h₁⟩ else
      match decidableBEx p xs with
      | isTrue h₂ => isTrue <| let ⟨y, hm, hp⟩ := h₂; ⟨y, .tail _ hm, hp⟩
      | isFalse h₂ => isFalse fun
        | ⟨y, .tail _ h, hp⟩ => h₂ ⟨y, h, hp⟩
        | ⟨_, .head .., hp⟩ => h₁ hp

instance decidableBAll (p : α → Prop) [DecidablePred p] :
    ∀ l : List α, Decidable (∀ x, x ∈ l → p x)
  | [] => isTrue nofun
  | x :: xs =>
    if h₁ : p x then
      match decidableBAll p xs with
      | isTrue h₂ => isTrue fun
        | y, .tail _ h => h₂ y h
        | _, .head .. => h₁
      | isFalse h₂ => isFalse fun H => h₂ fun y hm => H y (.tail _ hm)
    else isFalse fun H => h₁ <| H x (.head ..)

/-! ## Sublists -/

/-! ### take -/

/--
`O(min n |xs|)`. Returns the first `n` elements of `xs`, or the whole list if `n` is too large.
* `take 0 [a, b, c, d, e] = []`
* `take 3 [a, b, c, d, e] = [a, b, c]`
* `take 6 [a, b, c, d, e] = [a, b, c, d, e]`
-/
def take : Nat → List α → List α
  | 0,   _     => []
  | _+1, []    => []
  | n+1, a::as => a :: take n as

@[simp] theorem take_nil : ([] : List α).take i = [] := by cases i <;> rfl
@[simp] theorem take_zero (l : List α) : l.take 0 = [] := rfl
@[simp] theorem take_succ_cons : (a::as).take (i+1) = a :: as.take i := rfl

/-! ### drop -/

/--
`O(min n |xs|)`. Removes the first `n` elements of `xs`.
* `drop 0 [a, b, c, d, e] = [a, b, c, d, e]`
* `drop 3 [a, b, c, d, e] = [d, e]`
* `drop 6 [a, b, c, d, e] = []`
-/
def drop : Nat → List α → List α
  | 0,   a     => a
  | _+1, []    => []
  | n+1, _::as => drop n as

@[simp] theorem drop_nil : ([] : List α).drop i = [] := by
  cases i <;> rfl
@[simp] theorem drop_zero (l : List α) : l.drop 0 = l := rfl
@[simp] theorem drop_succ_cons : (a :: l).drop (n + 1) = l.drop n := rfl

theorem drop_eq_nil_of_le {as : List α} {i : Nat} (h : as.length ≤ i) : as.drop i = [] := by
  match as, i with
  | [],    i   => simp
  | _::_,  0   => simp at h
  | _::as, i+1 => simp only [length_cons] at h; exact @drop_eq_nil_of_le as i (Nat.le_of_succ_le_succ h)

/-! ### takeWhile -/

/--
`O(|xs|)`. Returns the longest initial segment of `xs` for which `p` returns true.
* `takeWhile (· > 5) [7, 6, 4, 8] = [7, 6]`
* `takeWhile (· > 5) [7, 6, 6, 8] = [7, 6, 6, 8]`
-/
def takeWhile (p : α → Bool) : (xs : List α) → List α
  | []       => []
  | hd :: tl => match p hd with
   | true  => hd :: takeWhile p tl
   | false => []

@[simp] theorem takeWhile_nil : ([] : List α).takeWhile p = [] := rfl

/-! ### dropWhile -/

/--
`O(|l|)`. `dropWhile p l` removes elements from the list until it finds the first element
for which `p` returns false; this element and everything after it is returned.
```
dropWhile (· < 4) [1, 3, 2, 4, 2, 7, 4] = [4, 2, 7, 4]
```
-/
def dropWhile (p : α → Bool) : List α → List α
  | []   => []
  | a::l => match p a with
    | true  => dropWhile p l
    | false => a::l

@[simp] theorem dropWhile_nil : ([] : List α).dropWhile p = [] := rfl

/-! ### partition -/

/--
`O(|l|)`. `partition p l` calls `p` on each element of `l`, partitioning the list into two lists
`(l_true, l_false)` where `l_true` has the elements where `p` was true
and `l_false` has the elements where `p` is false.
`partition p l = (filter p l, filter (not ∘ p) l)`, but it is slightly more efficient
since it only has to do one pass over the list.
```
partition (· > 2) [1, 2, 5, 2, 7, 7] = ([5, 7, 7], [1, 2, 2])
```
-/
@[inline] def partition (p : α → Bool) (as : List α) : List α × List α :=
  loop as ([], [])
where
  @[specialize] loop : List α → List α × List α → List α × List α
  | [],    (bs, cs) => (bs.reverse, cs.reverse)
  | a::as, (bs, cs) =>
    match p a with
    | true  => loop as (a::bs, cs)
    | false => loop as (bs, a::cs)

/-! ### dropLast -/

/--
Removes the last element of the list.
* `dropLast [] = []`
* `dropLast [a] = []`
* `dropLast [a, b, c] = [a, b]`
-/
def dropLast {α} : List α → List α
  | []    => []
  | [_]   => []
  | a::as => a :: dropLast as

@[simp] theorem dropLast_nil : ([] : List α).dropLast = [] := rfl
@[simp] theorem dropLast_single : [x].dropLast = [] := rfl
@[simp] theorem dropLast_cons₂ :
    (x::y::zs).dropLast = x :: (y::zs).dropLast := rfl

-- Later this can be proved by `simp` via `[List.length_dropLast, List.length_cons, Nat.add_sub_cancel]`,
-- but we need this while bootstrapping `Array`.
@[simp] theorem length_dropLast_cons (a : α) (as : List α) : (a :: as).dropLast.length = as.length := by
  match as with
  | []       => rfl
  | b::bs =>
    have ih := length_dropLast_cons b bs
    simp [dropLast, ih]

/-! ### Subset -/

/--
`l₁ ⊆ l₂` means that every element of `l₁` is also an element of `l₂`, ignoring multiplicity.
-/
protected def Subset (l₁ l₂ : List α) := ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂

instance : HasSubset (List α) := ⟨List.Subset⟩

instance [DecidableEq α] : DecidableRel (Subset : List α → List α → Prop) :=
  fun _ _ => decidableBAll _ _

/-! ### Sublist and isSublist -/

/-- `l₁ <+ l₂`, or `Sublist l₁ l₂`, says that `l₁` is a (non-contiguous) subsequence of `l₂`. -/
inductive Sublist {α} : List α → List α → Prop
  /-- the base case: `[]` is a sublist of `[]` -/
  | slnil : Sublist [] []
  /-- If `l₁` is a subsequence of `l₂`, then it is also a subsequence of `a :: l₂`. -/
  | cons a : Sublist l₁ l₂ → Sublist l₁ (a :: l₂)
  /-- If `l₁` is a subsequence of `l₂`, then `a :: l₁` is a subsequence of `a :: l₂`. -/
  | cons₂ a : Sublist l₁ l₂ → Sublist (a :: l₁) (a :: l₂)

@[inherit_doc] scoped infixl:50 " <+ " => Sublist

/-- True if the first list is a potentially non-contiguous sub-sequence of the second list. -/
def isSublist [BEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | l₁@(hd₁::tl₁), hd₂::tl₂ =>
    if hd₁ == hd₂
    then tl₁.isSublist tl₂
    else l₁.isSublist tl₂

/-! ### IsPrefix / isPrefixOf / isPrefixOf? -/

/--
`IsPrefix l₁ l₂`, or `l₁ <+: l₂`, means that `l₁` is a prefix of `l₂`,
that is, `l₂` has the form `l₁ ++ t` for some `t`.
-/
def IsPrefix (l₁ : List α) (l₂ : List α) : Prop := Exists fun t => l₁ ++ t = l₂

@[inherit_doc] infixl:50 " <+: " => IsPrefix

/--  `isPrefixOf l₁ l₂` returns `true` Iff `l₁` is a prefix of `l₂`.
That is, there exists a `t` such that `l₂ == l₁ ++ t`. -/
def isPrefixOf [BEq α] : List α → List α → Bool
  | [],    _     => true
  | _,     []    => false
  | a::as, b::bs => a == b && isPrefixOf as bs

@[simp] theorem isPrefixOf_nil_left [BEq α] : isPrefixOf ([] : List α) l = true := by
  simp [isPrefixOf]
@[simp] theorem isPrefixOf_cons_nil [BEq α] : isPrefixOf (a::as) ([] : List α) = false := rfl
theorem isPrefixOf_cons₂ [BEq α] {a : α} :
    isPrefixOf (a::as) (b::bs) = (a == b && isPrefixOf as bs) := rfl

/-- `isPrefixOf? l₁ l₂` returns `some t` when `l₂ == l₁ ++ t`. -/
def isPrefixOf? [BEq α] : List α → List α → Option (List α)
  | [], l₂ => some l₂
  | _, [] => none
  | (x₁ :: l₁), (x₂ :: l₂) =>
    if x₁ == x₂ then isPrefixOf? l₁ l₂ else none

/-! ### IsSuffix / isSuffixOf / isSuffixOf? -/

/--  `isSuffixOf l₁ l₂` returns `true` Iff `l₁` is a suffix of `l₂`.
That is, there exists a `t` such that `l₂ == t ++ l₁`. -/
def isSuffixOf [BEq α] (l₁ l₂ : List α) : Bool :=
  isPrefixOf l₁.reverse l₂.reverse

@[simp] theorem isSuffixOf_nil_left [BEq α] : isSuffixOf ([] : List α) l = true := by
  simp [isSuffixOf]

/-- `isSuffixOf? l₁ l₂` returns `some t` when `l₂ == t ++ l₁`.-/
def isSuffixOf? [BEq α] (l₁ l₂ : List α) : Option (List α) :=
  Option.map List.reverse <| isPrefixOf? l₁.reverse l₂.reverse

/--
`IsSuffix l₁ l₂`, or `l₁ <:+ l₂`, means that `l₁` is a suffix of `l₂`,
that is, `l₂` has the form `t ++ l₁` for some `t`.
-/
def IsSuffix (l₁ : List α) (l₂ : List α) : Prop := Exists fun t => t ++ l₁ = l₂

@[inherit_doc] infixl:50 " <:+ " => IsSuffix

/-! ### IsInfix -/

/--
`IsInfix l₁ l₂`, or `l₁ <:+: l₂`, means that `l₁` is a contiguous
substring of `l₂`, that is, `l₂` has the form `s ++ l₁ ++ t` for some `s, t`.
-/
def IsInfix (l₁ : List α) (l₂ : List α) : Prop := Exists fun s => Exists fun t => s ++ l₁ ++ t = l₂

@[inherit_doc] infixl:50 " <:+: " => IsInfix

/-! ### splitAt -/

/--
Split a list at an index.
```
splitAt 2 [a, b, c] = ([a, b], [c])
```
-/
def splitAt (n : Nat) (l : List α) : List α × List α := go l n [] where
  /--
  Auxiliary for `splitAt`:
  `splitAt.go l xs n acc = (acc.reverse ++ take n xs, drop n xs)` if `n < xs.length`,
  and `(l, [])` otherwise.
  -/
  go : List α → Nat → List α → List α × List α
  | [], _, _ => (l, []) -- This branch ensures the pointer equality of the result with the input
                        -- without any runtime branching cost.
  | x :: xs, n+1, acc => go xs n (x :: acc)
  | xs, _, acc => (acc.reverse, xs)

/-! ### rotateLeft -/

/--
`O(n)`. Rotates the elements of `xs` to the left such that the element at
`xs[i]` rotates to `xs[(i - n) % l.length]`.
* `rotateLeft [1, 2, 3, 4, 5] 3 = [4, 5, 1, 2, 3]`
* `rotateLeft [1, 2, 3, 4, 5] 5 = [1, 2, 3, 4, 5]`
* `rotateLeft [1, 2, 3, 4, 5] = [2, 3, 4, 5, 1]`
-/
def rotateLeft (xs : List α) (n : Nat := 1) : List α :=
  let len := xs.length
  if len ≤ 1 then
    xs
  else
    let n := n % len
    let b := xs.take n
    let e := xs.drop n
    e ++ b

@[simp] theorem rotateLeft_nil : ([] : List α).rotateLeft n = [] := rfl

/-! ### rotateRight -/

/--
`O(n)`. Rotates the elements of `xs` to the right such that the element at
`xs[i]` rotates to `xs[(i + n) % l.length]`.
* `rotateRight [1, 2, 3, 4, 5] 3 = [3, 4, 5, 1, 2]`
* `rotateRight [1, 2, 3, 4, 5] 5 = [1, 2, 3, 4, 5]`
* `rotateRight [1, 2, 3, 4, 5] = [5, 1, 2, 3, 4]`
-/
def rotateRight (xs : List α) (n : Nat := 1) : List α :=
  let len := xs.length
  if len ≤ 1 then
    xs
  else
    let n := len - n % len
    let b := xs.take n
    let e := xs.drop n
    e ++ b

@[simp] theorem rotateRight_nil : ([] : List α).rotateRight n = [] := rfl

/-! ## Pairwise, Nodup -/

section Pairwise

variable (R : α → α → Prop)

/--
`Pairwise R l` means that all the elements with earlier indexes are
`R`-related to all the elements with later indexes.
```
Pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3
```
For example if `R = (·≠·)` then it asserts `l` has no duplicates,
and if `R = (·<·)` then it asserts that `l` is (strictly) sorted.
-/
inductive Pairwise : List α → Prop
  /-- All elements of the empty list are vacuously pairwise related. -/
  | nil : Pairwise []
  /-- `a :: l` is `Pairwise R` if `a` `R`-relates to every element of `l`,
  and `l` is `Pairwise R`. -/
  | cons : ∀ {a : α} {l : List α}, (∀ a', a' ∈ l → R a a') → Pairwise l → Pairwise (a :: l)

attribute [simp] Pairwise.nil

variable {R}

@[simp] theorem pairwise_cons : Pairwise R (a::l) ↔ (∀ a', a' ∈ l → R a a') ∧ Pairwise R l :=
  ⟨fun | .cons h₁ h₂ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => h₂.cons h₁⟩

instance instDecidablePairwise [DecidableRel R] :
    (l : List α) → Decidable (Pairwise R l)
  | [] => isTrue .nil
  | hd :: tl =>
    match instDecidablePairwise tl with
    | isTrue ht =>
      match decidableBAll (R hd) tl with
      | isFalse hf => isFalse fun hf' => hf (pairwise_cons.1 hf').1
      | isTrue ht' => isTrue <| pairwise_cons.mpr (And.intro ht' ht)
    | isFalse hf => isFalse fun | .cons _ ih => hf ih

end Pairwise

/-- `Nodup l` means that `l` has no duplicates, that is, any element appears at most
  once in the List. It is defined as `Pairwise (≠)`. -/
def Nodup : List α → Prop := Pairwise (· ≠ ·)

instance nodupDecidable [DecidableEq α] : ∀ l : List α, Decidable (Nodup l) :=
  instDecidablePairwise

/-! ## Manipulating elements -/

/-! ### replace -/

/--
`O(|l|)`. `replace l a b` replaces the first element in the list equal to `a` with `b`.

* `replace [1, 4, 2, 3, 3, 7] 3 6 = [1, 4, 2, 6, 3, 7]`
* `replace [1, 4, 2, 3, 3, 7] 5 6 = [1, 4, 2, 3, 3, 7]`
-/
def replace [BEq α] : List α → α → α → List α
  | [],    _, _ => []
  | a::as, b, c => match b == a with
    | true  => c::as
    | false => a :: replace as b c

@[simp] theorem replace_nil [BEq α] : ([] : List α).replace a b = [] := rfl
theorem replace_cons [BEq α] {a : α} :
    (a::as).replace b c = match b == a with | true => c::as | false => a :: replace as b c :=
  rfl

/-! ### modify -/

/--
Apply a function to the nth tail of `l`. Returns the input without
using `f` if the index is larger than the length of the List.
```
modifyTailIdx f 2 [a, b, c] = [a, b] ++ f [c]
```
-/
@[simp] def modifyTailIdx (f : List α → List α) : Nat → List α → List α
  | 0, l => f l
  | _+1, [] => []
  | n+1, a :: l => a :: modifyTailIdx f n l

/-- Apply `f` to the head of the list, if it exists. -/
@[inline] def modifyHead (f : α → α) : List α → List α
  | [] => []
  | a :: l => f a :: l

@[simp] theorem modifyHead_nil (f : α → α) : [].modifyHead f = [] := by rw [modifyHead]
@[simp] theorem modifyHead_cons (a : α) (l : List α) (f : α → α) :
    (a :: l).modifyHead f = f a :: l := by rw [modifyHead]

/--
Apply `f` to the nth element of the list, if it exists, replacing that element with the result.
-/
def modify (f : α → α) : Nat → List α → List α :=
  modifyTailIdx (modifyHead f)

/-! ### insert -/

/-- Inserts an element into a list without duplication. -/
@[inline] protected def insert [BEq α] (a : α) (l : List α) : List α :=
  if l.elem a then l else a :: l

/--
`insertIdx n a l` inserts `a` into the list `l` after the first `n` elements of `l`
```
insertIdx 2 1 [1, 2, 3, 4] = [1, 2, 1, 3, 4]
```
-/
def insertIdx (n : Nat) (a : α) : List α → List α :=
  modifyTailIdx (cons a) n

/-! ### erase -/

/--
`O(|l|)`. `erase l a` removes the first occurrence of `a` from `l`.
* `erase [1, 5, 3, 2, 5] 5 = [1, 3, 2, 5]`
* `erase [1, 5, 3, 2, 5] 6 = [1, 5, 3, 2, 5]`
-/
protected def erase {α} [BEq α] : List α → α → List α
  | [],    _ => []
  | a::as, b => match a == b with
    | true  => as
    | false => a :: List.erase as b

@[simp] theorem erase_nil [BEq α] (a : α) : [].erase a = [] := rfl
theorem erase_cons [BEq α] (a b : α) (l : List α) :
    (b :: l).erase a = if b == a then l else b :: l.erase a := by
  simp only [List.erase]; split <;> simp_all

/-- `eraseP p l` removes the first element of `l` satisfying the predicate `p`. -/
def eraseP (p : α → Bool) : List α → List α
  | [] => []
  | a :: l => bif p a then l else a :: eraseP p l

/-! ### eraseIdx -/

/--
`O(i)`. `eraseIdx l i` removes the `i`'th element of the list `l`.
* `erase [a, b, c, d, e] 0 = [b, c, d, e]`
* `erase [a, b, c, d, e] 1 = [a, c, d, e]`
* `erase [a, b, c, d, e] 5 = [a, b, c, d, e]`
-/
def eraseIdx : List α → Nat → List α
  | [],    _   => []
  | _::as, 0   => as
  | a::as, n+1 => a :: eraseIdx as n

@[simp] theorem eraseIdx_nil : ([] : List α).eraseIdx i = [] := rfl
@[simp] theorem eraseIdx_cons_zero : (a::as).eraseIdx 0 = as := rfl
@[simp] theorem eraseIdx_cons_succ : (a::as).eraseIdx (i+1) = a :: as.eraseIdx i := rfl

/-! Finding elements -/

/-! ### find? -/

/--
`O(|l|)`. `find? p l` returns the first element for which `p` returns true,
or `none` if no such element is found.

* `find? (· < 5) [7, 6, 5, 8, 1, 2, 6] = some 1`
* `find? (· < 1) [7, 6, 5, 8, 1, 2, 6] = none`
-/
def find? (p : α → Bool) : List α → Option α
  | []    => none
  | a::as => match p a with
    | true  => some a
    | false => find? p as

@[simp] theorem find?_nil : ([] : List α).find? p = none := rfl
theorem find?_cons : (a::as).find? p = match p a with | true => some a | false => as.find? p :=
  rfl

/-! ### findSome? -/

/--
`O(|l|)`. `findSome? f l` applies `f` to each element of `l`, and returns the first non-`none` result.

* `findSome? (fun x => if x < 5 then some (10 * x) else none) [7, 6, 5, 8, 1, 2, 6] = some 10`
-/
def findSome? (f : α → Option β) : List α → Option β
  | []    => none
  | a::as => match f a with
    | some b => some b
    | none   => findSome? f as

@[simp] theorem findSome?_nil : ([] : List α).findSome? f = none := rfl
theorem findSome?_cons {f : α → Option β} :
    (a::as).findSome? f = match f a with | some b => some b | none => as.findSome? f :=
  rfl

/-! ### findIdx -/

/-- Returns the index of the first element satisfying `p`, or the length of the list otherwise. -/
@[inline] def findIdx (p : α → Bool) (l : List α) : Nat := go l 0 where
  /-- Auxiliary for `findIdx`: `findIdx.go p l n = findIdx p l + n` -/
  @[specialize] go : List α → Nat → Nat
  | [], n => n
  | a :: l, n => bif p a then n else go l (n + 1)

@[simp] theorem findIdx_nil {α : Type _} (p : α → Bool) : [].findIdx p = 0 := rfl

/-! ### indexOf -/

/-- Returns the index of the first element equal to `a`, or the length of the list otherwise. -/
def indexOf [BEq α] (a : α) : List α → Nat := findIdx (· == a)

@[simp] theorem indexOf_nil [BEq α] : ([] : List α).indexOf x = 0 := rfl

/-! ### findIdx? -/

/-- Return the index of the first occurrence of an element satisfying `p`. -/
def findIdx? (p : α → Bool) : List α → (start : Nat := 0) → Option Nat
| [], _ => none
| a :: l, i => if p a then some i else findIdx? p l (i + 1)

/-! ### indexOf? -/

/-- Return the index of the first occurrence of `a` in the list. -/
@[inline] def indexOf? [BEq α] (a : α) : List α → Option Nat := findIdx? (· == a)

/-! ### countP -/

/-- `countP p l` is the number of elements of `l` that satisfy `p`. -/
@[inline] def countP (p : α → Bool) (l : List α) : Nat := go l 0 where
  /-- Auxiliary for `countP`: `countP.go p l acc = countP p l + acc`. -/
  @[specialize] go : List α → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => bif p x then go xs (acc + 1) else go xs acc

/-! ### count -/

/-- `count a l` is the number of occurrences of `a` in `l`. -/
@[inline] def count [BEq α] (a : α) : List α → Nat := countP (· == a)

/-! ### lookup -/

/--
`O(|l|)`. `lookup a l` treats `l : List (α × β)` like an association list,
and returns the first `β` value corresponding to an `α` value in the list equal to `a`.

* `lookup 3 [(1, 2), (3, 4), (3, 5)] = some 4`
* `lookup 2 [(1, 2), (3, 4), (3, 5)] = none`
-/
def lookup [BEq α] : α → List (α × β) → Option β
  | _, []        => none
  | a, (k,b)::es => match a == k with
    | true  => some b
    | false => lookup a es

@[simp] theorem lookup_nil [BEq α] : ([] : List (α × β)).lookup a = none := rfl
theorem lookup_cons [BEq α] {k : α} :
    ((k,b)::es).lookup a = match a == k with | true => some b | false => es.lookup a :=
  rfl

/-! ## Permutations -/

/-! ### Perm -/

/--
`Perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
of each other. This is defined by induction using pairwise swaps.
-/
inductive Perm : List α → List α → Prop
  /-- `[] ~ []` -/
  | nil : Perm [] []
  /-- `l₁ ~ l₂ → x::l₁ ~ x::l₂` -/
  | cons (x : α) {l₁ l₂ : List α} : Perm l₁ l₂ → Perm (x :: l₁) (x :: l₂)
  /-- `x::y::l ~ y::x::l` -/
  | swap (x y : α) (l : List α) : Perm (y :: x :: l) (x :: y :: l)
  /-- `Perm` is transitive. -/
  | trans {l₁ l₂ l₃ : List α} : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

@[inherit_doc] scoped infixl:50 " ~ " => Perm

/-! ### isPerm -/

/--
`O(|l₁| * |l₂|)`. Computes whether `l₁` is a permutation of `l₂`. See `isPerm_iff` for a
characterization in terms of `List.Perm`.
-/
def isPerm [BEq α] : List α → List α → Bool
  | [], l₂ => l₂.isEmpty
  | a :: l₁, l₂ => l₂.contains a && l₁.isPerm (l₂.erase a)

/-! ## Logical operations -/

/-! ### any -/

/--
`O(|l|)`. Returns true if `p` is true for any element of `l`.
* `any p [a, b, c] = p a || p b || p c`

Short-circuits upon encountering the first `true`.
-/
def any : List α → (α → Bool) → Bool
  | [], _ => false
  | h :: t, p => p h || any t p

@[simp] theorem any_nil : [].any f = false := rfl
@[simp] theorem any_cons : (a::l).any f = (f a || l.any f) := rfl

/-! ### all -/

/--
`O(|l|)`. Returns true if `p` is true for every element of `l`.
* `all p [a, b, c] = p a && p b && p c`

Short-circuits upon encountering the first `false`.
-/
def all : List α → (α → Bool) → Bool
  | [], _ => true
  | h :: t, p => p h && all t p

@[simp] theorem all_nil : [].all f = true := rfl
@[simp] theorem all_cons : (a::l).all f = (f a && l.all f) := rfl

/-! ### or -/

/--
`O(|l|)`. Returns true if `true` is an element of the list of booleans `l`.
* `or [a, b, c] = a || b || c`
-/
def or (bs : List Bool) : Bool := bs.any id

@[simp] theorem or_nil : [].or = false := rfl
@[simp] theorem or_cons : (a::l).or = (a || l.or) := rfl

/-! ### and -/

/--
`O(|l|)`. Returns true if every element of `l` is the value `true`.
* `and [a, b, c] = a && b && c`
-/
def and (bs : List Bool) : Bool := bs.all id

@[simp] theorem and_nil : [].and = true := rfl
@[simp] theorem and_cons : (a::l).and = (a && l.and) := rfl

/-! ## Zippers -/

/-! ### zipWith -/

/--
`O(min |xs| |ys|)`. Applies `f` to the two lists in parallel, stopping at the shorter list.
* `zipWith f [x₁, x₂, x₃] [y₁, y₂, y₃, y₄] = [f x₁ y₁, f x₂ y₂, f x₃ y₃]`
-/
@[specialize] def zipWith (f : α → β → γ) : (xs : List α) → (ys : List β) → List γ
  | x::xs, y::ys => f x y :: zipWith f xs ys
  | _,     _     => []

@[simp] theorem zipWith_nil_left {f : α → β → γ} : zipWith f [] l = [] := rfl
@[simp] theorem zipWith_nil_right {f : α → β → γ} : zipWith f l [] = [] := by simp [zipWith]
@[simp] theorem zipWith_cons_cons {f : α → β → γ} :
    zipWith f (a :: as) (b :: bs) = f a b :: zipWith f as bs := rfl

/-! ### zip -/

/--
`O(min |xs| |ys|)`. Combines the two lists into a list of pairs, with one element from each list.
The longer list is truncated to match the shorter list.
* `zip [x₁, x₂, x₃] [y₁, y₂, y₃, y₄] = [(x₁, y₁), (x₂, y₂), (x₃, y₃)]`
-/
def zip : List α → List β → List (Prod α β) :=
  zipWith Prod.mk

@[simp] theorem zip_nil_left : zip ([] : List α) (l : List β)  = [] := rfl
@[simp] theorem zip_nil_right : zip (l : List α) ([] : List β)  = [] := by simp [zip, zipWith]
@[simp] theorem zip_cons_cons : zip (a :: as) (b :: bs) = (a, b) :: zip as bs := rfl

/-! ### zipWithAll -/

/--
`O(max |xs| |ys|)`.
Version of `List.zipWith` that continues to the end of both lists,
passing `none` to one argument once the shorter list has run out.
-/
def zipWithAll (f : Option α → Option β → γ) : List α → List β → List γ
  | [], bs => bs.map fun b => f none (some b)
  | a :: as, [] => (a :: as).map fun a => f (some a) none
  | a :: as, b :: bs => f a b :: zipWithAll f as bs

@[simp] theorem zipWithAll_nil_right :
    zipWithAll f as [] = as.map fun a => f (some a) none := by
  cases as <;> rfl
@[simp] theorem zipWithAll_nil_left :
    zipWithAll f [] bs = bs.map fun b => f none (some b) := rfl
@[simp] theorem zipWithAll_cons_cons :
    zipWithAll f (a :: as) (b :: bs) = f (some a) (some b) :: zipWithAll f as bs := rfl

/-! ### unzip -/

/--
`O(|l|)`. Separates a list of pairs into two lists containing the first components and second components.
* `unzip [(x₁, y₁), (x₂, y₂), (x₃, y₃)] = ([x₁, x₂, x₃], [y₁, y₂, y₃])`
-/
def unzip : List (α × β) → List α × List β
  | []          => ([], [])
  | (a, b) :: t => match unzip t with | (al, bl) => (a::al, b::bl)

@[simp] theorem unzip_nil : ([] : List (α × β)).unzip = ([], []) := rfl
@[simp] theorem unzip_cons {h : α × β} :
    (h :: t).unzip = match unzip t with | (al, bl) => (h.1::al, h.2::bl) := rfl

/-! ## Ranges and enumeration -/

/-- Sum of a list.

`List.sum [a, b, c] = a + (b + (c + 0))` -/
def sum {α} [Add α] [Zero α] : List α → α :=
  foldr (· + ·) 0

@[simp] theorem sum_nil [Add α] [Zero α] : ([] : List α).sum = 0 := rfl
@[simp] theorem sum_cons [Add α] [Zero α] {a : α} {l : List α} : (a::l).sum = a + l.sum := rfl

/-- Sum of a list of natural numbers. -/
@[deprecated List.sum (since := "2024-10-17")]
protected def _root_.Nat.sum (l : List Nat) : Nat := l.foldr (·+·) 0

set_option linter.deprecated false in
@[simp, deprecated sum_nil (since := "2024-10-17")]
theorem _root_.Nat.sum_nil : Nat.sum ([] : List Nat) = 0 := rfl
set_option linter.deprecated false in
@[simp, deprecated sum_cons (since := "2024-10-17")]
theorem _root_.Nat.sum_cons (a : Nat) (l : List Nat) :
    Nat.sum (a::l) = a + Nat.sum l := rfl

/-! ### range -/

/--
`O(n)`. `range n` is the numbers from `0` to `n` exclusive, in increasing order.
* `range 5 = [0, 1, 2, 3, 4]`
-/
def range (n : Nat) : List Nat :=
  loop n []
where
  loop : Nat → List Nat → List Nat
  | 0,   ns => ns
  | n+1, ns => loop n (n::ns)

@[simp] theorem range_zero : range 0 = [] := rfl

/-! ### range' -/

/-- `range' start len step` is the list of numbers `[start, start+step, ..., start+(len-1)*step]`.
  It is intended mainly for proving properties of `range` and `iota`. -/
def range' : (start len : Nat) → (step : Nat := 1) → List Nat
  | _, 0, _ => []
  | s, n+1, step => s :: range' (s+step) n step

/-! ### iota -/

/--
`O(n)`. `iota n` is the numbers from `1` to `n` inclusive, in decreasing order.
* `iota 5 = [5, 4, 3, 2, 1]`
-/
def iota : Nat → List Nat
  | 0       => []
  | m@(n+1) => m :: iota n

@[simp] theorem iota_zero : iota 0 = [] := rfl
@[simp] theorem iota_succ : iota (i+1) = (i+1) :: iota i := rfl

/-! ### enumFrom -/

/--
`O(|l|)`. `enumFrom n l` is like `enum` but it allows you to specify the initial index.
* `enumFrom 5 [a, b, c] = [(5, a), (6, b), (7, c)]`
-/
def enumFrom : Nat → List α → List (Nat × α)
  | _, [] => nil
  | n, x :: xs   => (n, x) :: enumFrom (n + 1) xs

@[simp] theorem enumFrom_nil : ([] : List α).enumFrom i = [] := rfl
@[simp] theorem enumFrom_cons : (a::as).enumFrom i = (i, a) :: as.enumFrom (i+1) := rfl

/-! ### enum -/

/--
`O(|l|)`. `enum l` pairs up each element with its index in the list.
* `enum [a, b, c] = [(0, a), (1, b), (2, c)]`
-/
def enum : List α → List (Nat × α) := enumFrom 0

@[simp] theorem enum_nil : ([] : List α).enum = [] := rfl

/-! ## Minima and maxima -/

/-! ### min? -/

/--
Returns the smallest element of the list, if it is not empty.
* `[].min? = none`
* `[4].min? = some 4`
* `[1, 4, 2, 10, 6].min? = some 1`
-/
def min? [Min α] : List α → Option α
  | []    => none
  | a::as => some <| as.foldl min a

@[inherit_doc min?, deprecated min? (since := "2024-09-29")] abbrev minimum? := @min?

/-! ### max? -/

/--
Returns the largest element of the list, if it is not empty.
* `[].max? = none`
* `[4].max? = some 4`
* `[1, 4, 2, 10, 6].max? = some 10`
-/
def max? [Max α] : List α → Option α
  | []    => none
  | a::as => some <| as.foldl max a

@[inherit_doc max?, deprecated max? (since := "2024-09-29")] abbrev maximum? := @max?

/-! ## Other list operations

The functions are currently mostly used in meta code,
and do not have sufficient API developed for verification work.
-/

/-! ### intersperse -/

/--
`O(|l|)`. `intersperse sep l` alternates `sep` and the elements of `l`:
* `intersperse sep [] = []`
* `intersperse sep [a] = [a]`
* `intersperse sep [a, b] = [a, sep, b]`
* `intersperse sep [a, b, c] = [a, sep, b, sep, c]`
-/
def intersperse (sep : α) : List α → List α
  | []    => []
  | [x]   => [x]
  | x::xs => x :: sep :: intersperse sep xs

@[simp] theorem intersperse_nil (sep : α) : ([] : List α).intersperse sep = [] := rfl
@[simp] theorem intersperse_single (sep : α) : [x].intersperse sep = [x] := rfl
@[simp] theorem intersperse_cons₂ (sep : α) :
    (x::y::zs).intersperse sep = x::sep::((y::zs).intersperse sep) := rfl

/-! ### intercalate -/

/--
`O(|xs|)`. `intercalate sep xs` alternates `sep` and the elements of `xs`:
* `intercalate sep [] = []`
* `intercalate sep [a] = a`
* `intercalate sep [a, b] = a ++ sep ++ b`
* `intercalate sep [a, b, c] = a ++ sep ++ b ++ sep ++ c`
-/
def intercalate (sep : List α) (xs : List (List α)) : List α :=
  (intersperse sep xs).flatten

/-! ### eraseDups -/

/-- `O(|l|^2)`. Erase duplicated elements in the list.
Keeps the first occurrence of duplicated elements.
* `eraseDups [1, 3, 2, 2, 3, 5] = [1, 3, 2, 5]`
-/
def eraseDups {α} [BEq α] (as : List α) : List α :=
  loop as []
where
  loop : List α → List α → List α
  | [],    bs => bs.reverse
  | a::as, bs => match bs.elem a with
    | true  => loop as bs
    | false => loop as (a::bs)

/-! ### eraseReps -/

/--
`O(|l|)`. Erase repeated adjacent elements. Keeps the first occurrence of each run.
* `eraseReps [1, 3, 2, 2, 2, 3, 5] = [1, 3, 2, 3, 5]`
-/
def eraseReps {α} [BEq α] : List α → List α
  | []    => []
  | a::as => loop a as []
where
  loop {α} [BEq α] : α → List α → List α → List α
  | a, [], rs => (a::rs).reverse
  | a, a'::as, rs => match a == a' with
    | true  => loop a as rs
    | false => loop a' as (a::rs)

/-! ### span -/

/--
`O(|l|)`. `span p l` splits the list `l` into two parts, where the first part
contains the longest initial segment for which `p` returns true
and the second part is everything else.

* `span (· > 5) [6, 8, 9, 5, 2, 9] = ([6, 8, 9], [5, 2, 9])`
* `span (· > 10) [6, 8, 9, 5, 2, 9] = ([], [6, 8, 9, 5, 2, 9])`
-/
@[inline] def span (p : α → Bool) (as : List α) : List α × List α :=
  loop as []
where
  @[specialize] loop : List α → List α → List α × List α
  | [],    rs => (rs.reverse, [])
  | a::as, rs => match p a with
    | true  => loop as (a::rs)
    | false => (rs.reverse, a::as)

/-! ### splitBy -/

/--
`O(|l|)`. `splitBy R l` splits `l` into chains of elements
such that adjacent elements are related by `R`.

* `splitBy (·==·) [1, 1, 2, 2, 2, 3, 2] = [[1, 1], [2, 2, 2], [3], [2]]`
* `splitBy (·<·) [1, 2, 5, 4, 5, 1, 4] = [[1, 2, 5], [4, 5], [1, 4]]`
-/
@[specialize] def splitBy (R : α → α → Bool) : List α → List (List α)
  | []    => []
  | a::as => loop as a [] []
where
  /--
  The arguments of `splitBy.loop l ag g gs` represent the following:

  - `l : List α` are the elements which we still need to split.
  - `ag : α` is the previous element for which a comparison was performed.
  - `g : List α` is the group currently being assembled, in **reverse order**.
  - `gs : List (List α)` is all of the groups that have been completed, in **reverse order**.
  -/
  @[specialize] loop : List α → α → List α → List (List α) → List (List α)
  | a::as, ag, g, gs => match R ag a with
    | true  => loop as a (ag::g) gs
    | false => loop as a [] ((ag::g).reverse::gs)
  | [], ag, g, gs => ((ag::g).reverse::gs).reverse

@[deprecated splitBy (since := "2024-10-30"), inherit_doc splitBy] abbrev groupBy := @splitBy

/-! ### removeAll -/

/-- `O(|xs|)`. Computes the "set difference" of lists,
by filtering out all elements of `xs` which are also in `ys`.
* `removeAll [1, 1, 5, 1, 2, 4, 5] [1, 2, 2] = [5, 4, 5]`
 -/
def removeAll [BEq α] (xs ys : List α) : List α :=
  xs.filter (fun x => !ys.elem x)

/-!
# Runtime re-implementations using `@[csimp]`

More of these re-implementations are provided in `Init/Data/List/Impl.lean`.
They can not be here, because the remaining ones required `Array` for their implementation.

This leaves a dangerous situation: if you import this file, but not `Init/Data/List/Impl.lean`,
then at runtime you will get non tail-recursive versions.
-/

/-! ### length -/

theorem length_add_eq_lengthTRAux (as : List α) (n : Nat) : as.length + n = as.lengthTRAux n := by
  induction as generalizing n with
  | nil  => simp [length, lengthTRAux]
  | cons a as ih =>
    simp [length, lengthTRAux, ← ih, Nat.succ_add]
    rfl

@[csimp] theorem length_eq_lengthTR : @List.length = @List.lengthTR := by
  apply funext; intro α; apply funext; intro as
  simp [lengthTR, ← length_add_eq_lengthTRAux]

/-! ### map -/

/-- Tail-recursive version of `List.map`. -/
@[inline] def mapTR (f : α → β) (as : List α) : List β :=
  loop as []
where
  @[specialize] loop : List α → List β → List β
  | [],    bs => bs.reverse
  | a::as, bs => loop as (f a :: bs)

theorem mapTR_loop_eq (f : α → β) (as : List α) (bs : List β) :
    mapTR.loop f as bs = bs.reverse ++ map f as := by
  induction as generalizing bs with
  | nil => simp [mapTR.loop, map]
  | cons a as ih =>
    simp only [mapTR.loop, map]
    rw [ih (f a :: bs), reverse_cons, append_assoc]
    rfl

@[csimp] theorem map_eq_mapTR : @map = @mapTR :=
  funext fun α => funext fun β => funext fun f => funext fun as => by
    simp [mapTR, mapTR_loop_eq]

/-! ### filter -/

/-- Tail-recursive version of `List.filter`. -/
@[inline] def filterTR (p : α → Bool) (as : List α) : List α :=
  loop as []
where
  @[specialize] loop : List α → List α → List α
  | [],    rs => rs.reverse
  | a::as, rs => match p a with
     | true  => loop as (a::rs)
     | false => loop as rs

theorem filterTR_loop_eq (p : α → Bool) (as bs : List α) :
    filterTR.loop p as bs = bs.reverse ++ filter p as := by
  induction as generalizing bs with
  | nil => simp [filterTR.loop, filter]
  | cons a as ih =>
    simp only [filterTR.loop, filter]
    split <;> simp_all

@[csimp] theorem filter_eq_filterTR : @filter = @filterTR := by
  apply funext; intro α; apply funext; intro p; apply funext; intro as
  simp [filterTR, filterTR_loop_eq]

/-! ### replicate -/

/-- Tail-recursive version of `List.replicate`. -/
def replicateTR {α : Type u} (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0, as => as
    | n+1, as => loop n (a::as)
  loop n []

theorem replicateTR_loop_replicate_eq (a : α) (m n : Nat) :
  replicateTR.loop a n (replicate m a) = replicate (n + m) a := by
  induction n generalizing m with simp [replicateTR.loop]
  | succ n ih => simp [Nat.succ_add]; exact ih (m+1)

theorem replicateTR_loop_eq : ∀ n, replicateTR.loop a n acc = replicate n a ++ acc
  | 0 => rfl
  | n+1 => by rw [← replicateTR_loop_replicate_eq _ 1 n, replicate, replicate,
    replicateTR.loop, replicateTR_loop_eq n, replicateTR_loop_eq n, append_assoc]; rfl

@[csimp] theorem replicate_eq_replicateTR : @List.replicate = @List.replicateTR := by
  apply funext; intro α; apply funext; intro n; apply funext; intro a
  exact (replicateTR_loop_replicate_eq _ 0 n).symm

/-! ## Additional functions -/

/-! ### leftpad -/

/-- Optimized version of `leftpad`. -/
@[inline] def leftpadTR (n : Nat) (a : α) (l : List α) : List α :=
  replicateTR.loop a (n - length l) l

@[csimp] theorem leftpad_eq_leftpadTR : @leftpad = @leftpadTR := by
  repeat (apply funext; intro)
  simp [leftpad, leftpadTR, replicateTR_loop_eq]


/-! ## Zippers -/

/-! ### unzip -/

/-- Tail recursive version of `List.unzip`. -/
def unzipTR (l : List (α × β)) : List α × List β :=
  l.foldr (fun (a, b) (al, bl) => (a::al, b::bl)) ([], [])

@[csimp] theorem unzip_eq_unzipTR : @unzip = @unzipTR := by
  apply funext; intro α; apply funext; intro β; apply funext; intro l
  simp [unzipTR]; induction l <;> simp [*]

/-! ## Ranges and enumeration -/

/-! ### range' -/

/-- Optimized version of `range'`. -/
@[inline] def range'TR (s n : Nat) (step : Nat := 1) : List Nat := go n (s + step * n) [] where
  /-- Auxiliary for `range'TR`: `range'TR.go n e = [e-n, ..., e-1] ++ acc`. -/
  go : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | n+1, e, acc => go n (e-step) ((e-step) :: acc)

@[csimp] theorem range'_eq_range'TR : @range' = @range'TR := by
  apply funext; intro s; apply funext; intro n; apply funext; intro step
  let rec go (s) : ∀ n m,
    range'TR.go step n (s + step * n) (range' (s + step * n) m step) = range' s (n + m) step
  | 0, m => by simp [range'TR.go]
  | n+1, m => by
    simp [range'TR.go]
    rw [Nat.mul_succ, ← Nat.add_assoc, Nat.add_sub_cancel, Nat.add_right_comm n]
    exact go s n (m + 1)
  exact (go s n 0).symm

/-! ### iota -/

/-- Tail-recursive version of `List.iota`. -/
def iotaTR (n : Nat) : List Nat :=
  let rec go : Nat → List Nat → List Nat
    | 0, r => r.reverse
    | m@(n+1), r => go n (m::r)
  go n []

@[csimp]
theorem iota_eq_iotaTR : @iota = @iotaTR :=
  have aux (n : Nat) (r : List Nat) : iotaTR.go n r = r.reverse ++ iota n := by
    induction n generalizing r with
    | zero => simp [iota, iotaTR.go]
    | succ n ih => simp [iota, iotaTR.go, ih, append_assoc]
  funext fun n => by simp [iotaTR, aux]

/-! ## Other list operations -/

/-! ### intersperse -/

/-- Tail recursive version of `List.intersperse`. -/
def intersperseTR (sep : α) : List α → List α
  | [] => []
  | [x] => [x]
  | x::y::xs => x :: sep :: y :: xs.foldr (fun a r => sep :: a :: r) []

@[csimp] theorem intersperse_eq_intersperseTR : @intersperse = @intersperseTR := by
  apply funext; intro α; apply funext; intro sep; apply funext; intro l
  simp [intersperseTR]
  match l with
  | [] | [_] => rfl
  | x::y::xs => simp [intersperse]; induction xs generalizing y <;> simp [*]

end List
