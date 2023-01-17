/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SimpLemmas
import Init.Data.Nat.Basic
set_option linter.missingDocs true -- keep it documented
open Decidable List

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

instance : GetElem (List α) Nat α fun as i => i < as.length where
  getElem as i h := as.get ⟨i, h⟩

@[simp] theorem cons_getElem_zero (a : α) (as : List α) (h : 0 < (a :: as).length) : getElem (a :: as) 0 h = a := by
  rfl

@[simp] theorem cons_getElem_succ (a : α) (as : List α) (i : Nat) (h : i + 1 < (a :: as).length) : getElem (a :: as) (i+1) h = getElem as i (Nat.lt_of_succ_lt_succ h) := by
  rfl

theorem length_add_eq_lengthTRAux (as : List α) (n : Nat) : as.length + n = as.lengthTRAux n := by
  induction as generalizing n with
  | nil  => simp [length, lengthTRAux]
  | cons a as ih =>
    simp [length, lengthTRAux, ← ih, Nat.succ_add]
    rfl

@[csimp] theorem length_eq_lengthTR : @List.length = @List.lengthTR := by
  apply funext; intro α; apply funext; intro as
  simp [lengthTR, ← length_add_eq_lengthTRAux]

@[simp] theorem length_nil : length ([] : List α) = 0 :=
  rfl

/-- Auxiliary for `List.reverse`. `List.reverseAux l r = l.reverse ++ r`, but it is defined directly. -/
def reverseAux : List α → List α → List α
  | [],   r => r
  | a::l, r => reverseAux l (a::r)

/--
`O(|as|)`. Reverse of a list:
* `[1, 2, 3, 4].reverse = [4, 3, 2, 1]`

Note that because of the "functional but in place" optimization implemented by Lean's compiler,
this function works without any allocations provided that the input list is unshared:
it simply walks the linked list and reverses all the node pointers.
-/
def reverse (as : List α) : List α :=
  reverseAux as []

theorem reverseAux_reverseAux_nil (as bs : List α) : reverseAux (reverseAux as bs) [] = reverseAux bs as := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => simp [reverseAux, ih]

theorem reverseAux_reverseAux (as bs cs : List α) : reverseAux (reverseAux as bs) cs = reverseAux bs (reverseAux (reverseAux as []) cs) := by
  induction as generalizing bs cs with
  | nil => rfl
  | cons a as ih => simp [reverseAux, ih (a::bs), ih [a]]

@[simp] theorem reverse_reverse (as : List α) : as.reverse.reverse = as := by
  simp [reverse]; rw [reverseAux_reverseAux_nil]; rfl

/--
`O(|xs|)`: append two lists. `[1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5]`.
It takes time proportional to the first list.
-/
protected def append : (xs ys : List α) → List α
  | [],    bs => bs
  | a::as, bs => a :: List.append as bs

/-- Tail-recursive version of `List.append`. -/
def appendTR (as bs : List α) : List α :=
  reverseAux as.reverse bs

@[csimp] theorem append_eq_appendTR : @List.append = @appendTR := by
  apply funext; intro α; apply funext; intro as; apply funext; intro bs
  simp [appendTR, reverse]
  induction as with
  | nil  => rfl
  | cons a as ih =>
    simp [reverseAux, List.append, ih, reverseAux_reverseAux]

instance : Append (List α) := ⟨List.append⟩

@[simp] theorem nil_append (as : List α) : [] ++ as = as := rfl
@[simp] theorem append_nil (as : List α) : as ++ [] = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp_all [HAppend.hAppend, Append.append, List.append]

@[simp] theorem cons_append (a : α) (as bs : List α) : (a::as) ++ bs = a::(as ++ bs) := rfl

@[simp] theorem append_eq (as bs : List α) : List.append as bs = as ++ bs := rfl

theorem append_assoc (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem append_cons (as : List α) (b : α) (bs : List α) : as ++ b :: bs = as ++ [b] ++ bs := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

instance : EmptyCollection (List α) := ⟨List.nil⟩

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

/--
`O(1)`. `isEmpty l` is true if the list is empty.
* `isEmpty [] = true`
* `isEmpty [a] = false`
* `isEmpty [a, b] = false`
-/
def isEmpty : List α → Bool
  | []     => true
  | _ :: _ => false

/--
`O(|l|)`. `map f l` applies `f` to each element of the list.
* `map f [a, b, c] = [f a, f b, f c]`
-/
@[specialize] def map (f : α → β) : List α → List β
  | []    => []
  | a::as => f a :: map f as

/-- Tail-recursive version of `List.map`. -/
@[inline] def mapTR (f : α → β) (as : List α) : List β :=
  loop as []
where
  @[specialize] loop : List α → List β → List β
  | [],    bs => bs.reverse
  | a::as, bs => loop as (f a :: bs)

theorem reverseAux_eq_append (as bs : List α) : reverseAux as bs = reverseAux as [] ++ bs := by
  induction as generalizing bs with
  | nil => simp [reverseAux]
  | cons a as ih =>
    simp [reverseAux]
    rw [ih (a :: bs), ih [a], append_assoc]
    rfl

@[simp] theorem reverse_nil : reverse ([] : List α) = [] :=
  rfl

@[simp] theorem reverse_cons (a : α) (as : List α) : reverse (a :: as) = reverse as ++ [a] := by
  simp [reverse, reverseAux]
  rw [← reverseAux_eq_append]

@[simp] theorem reverse_append (as bs : List α) : (as ++ bs).reverse = bs.reverse ++ as.reverse := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih => simp [ih]; rw [append_assoc]

theorem mapTR_loop_eq (f : α → β) (as : List α) (bs : List β) :
    mapTR.loop f as bs = bs.reverse ++ map f as := by
  induction as generalizing bs with
  | nil => simp [mapTR.loop, map]
  | cons a as ih =>
    simp [mapTR.loop, map]
    rw [ih (f a :: bs), reverse_cons, append_assoc]
    rfl

@[csimp] theorem map_eq_mapTR : @map = @mapTR :=
  funext fun α => funext fun β => funext fun f => funext fun as => by
    simp [mapTR, mapTR_loop_eq]

/--
`O(|join L|)`. `join L` concatenates all the lists in `L` into one list.
* `join [[a], [], [b, c], [d, e, f]] = [a, b, c, d, e, f]`
-/
def join : List (List α) → List α
  | []      => []
  | a :: as => a ++ join as

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
    simp [filterTR.loop, filter]
    split
    next => rw [ih, reverse_cons, append_assoc]; simp
    next => rw [ih]

@[csimp] theorem filter_eq_filterTR : @filter = @filterTR := by
  apply funext; intro α; apply funext; intro p; apply funext; intro as
  simp [filterTR, filterTR_loop_eq]

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

/--
`O(|l|)`. `findSome? f l` applies `f` to each element of `l`, and returns the first non-`none` result.

* `findSome? (fun x => if x < 5 then some (10 * x) else none) [7, 6, 5, 8, 1, 2, 6] = some 10`
-/
def findSome? (f : α → Option β) : List α → Option β
  | []    => none
  | a::as => match f a with
    | some b => some b
    | none   => findSome? f as

/--
`O(|l|)`. `replace l a b` replaces the first element in the list equal to `a` with `b`.

* `replace [1, 4, 2, 3, 3, 7] 3 6 = [1, 4, 2, 6, 3, 7]`
* `replace [1, 4, 2, 3, 3, 7] 5 6 = [1, 4, 2, 3, 3, 7]`
-/
def replace [BEq α] : List α → α → α → List α
  | [],    _, _ => []
  | a::as, b, c => match a == b with
    | true  => c::as
    | false => a :: replace as b c

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

/-- `notElem a l` is `!(elem a l)`. -/
def notElem [BEq α] (a : α) (as : List α) : Bool :=
  !(as.elem a)

@[inherit_doc elem] abbrev contains [BEq α] (as : List α) (a : α) : Bool :=
  elem a as

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
  mem := Mem

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

/--
`O(|l|)`. `span p l` splits the list `l` into two parts, where the first part
contains the longest initial segment for which `p` returns true
and the second part is everything else.

* `span (· > 5) [6, 8, 9, 5, 2, 9] = ([6, 8, 9], [5, 2, 9])`
* `span (· > 10) [6, 8, 9, 5, 2, 9] = ([6, 8, 9, 5, 2, 9], [])`
-/
@[inline] def span (p : α → Bool) (as : List α) : List α × List α :=
  loop as []
where
  @[specialize] loop : List α → List α → List α × List α
  | [],    rs => (rs.reverse, [])
  | a::as, rs => match p a with
    | true  => loop as (a::rs)
    | false => (rs.reverse, a::as)

/--
`O(|l|)`. `groupBy R l` splits `l` into chains of elements
such that adjacent elements are related by `R`.

* `groupBy (·==·) [1, 1, 2, 2, 2, 3, 2] = [[1, 1], [2, 2, 2], [3], [2]]`
* `groupBy (·<·) [1, 2, 5, 4, 5, 1, 4] = [[1, 2, 5], [4, 5], [1, 4]]`
-/
@[specialize] def groupBy (R : α → α → Bool) : List α → List (List α)
  | []    => []
  | a::as => loop as a [] []
where
  @[specialize] loop : List α → α → List α → List (List α) → List (List α)
  | a::as, ag, g, gs => match R ag a with
    | true  => loop as a (ag::g) gs
    | false => loop as a [] ((ag::g).reverse::gs)
  | [], ag, g, gs => ((ag::g).reverse::gs).reverse

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

/-- `O(|xs|)`. Computes the "set difference" of lists,
by filtering out all elements of `xs` which are also in `ys`.
* `removeAll [1, 1, 5, 1, 2, 4, 5] [1, 2, 2] = [5, 4, 5]`
 -/
def removeAll [BEq α] (xs ys : List α) : List α :=
  xs.filter (fun x => ys.notElem x)

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

theorem get_drop_eq_drop (as : List α) (i : Nat) (h : i < as.length) : as[i] :: as.drop (i+1) = as.drop i :=
  match as, i with
  | _::_, 0   => rfl
  | _::_, i+1 => get_drop_eq_drop _ i _

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

/--
`O(|l|)`. Applies function `f` to all of the elements of the list, from right to left.
* `foldr f init [a, b, c] = f a <| f b <| f c <| init`
-/
@[specialize] def foldr (f : α → β → β) (init : β) : List α → β
  | []     => init
  | a :: l => f a (foldr f init l)

/--
`O(|l|)`. Returns true if `p` is true for any element of `l`.
* `any p [a, b, c] = p a || p b || p c`
-/
@[inline] def any (l : List α) (p : α → Bool) : Bool :=
  foldr (fun a r => p a || r) false l

/--
`O(|l|)`. Returns true if `p` is true for every element of `l`.
* `all p [a, b, c] = p a && p b && p c`
-/
@[inline] def all (l : List α) (p : α → Bool) : Bool :=
  foldr (fun a r => p a && r) true l

/--
`O(|l|)`. Returns true if `true` is an element of the list of booleans `l`.
* `or [a, b, c] = a || b || c`
-/
def or  (bs : List Bool) : Bool := bs.any id

/--
`O(|l|)`. Returns true if every element of `l` is the value `true`.
* `and [a, b, c] = a && b && c`
-/
def and (bs : List Bool) : Bool := bs.all id

/--
`O(min |xs| |ys|)`. Applies `f` to the two lists in parallel, stopping at the shorter list.
* `zipWith f [x₁, x₂, x₃] [y₁, y₂, y₃, y₄] = [f x₁ y₁, f x₂ y₂, f x₃ y₃]`
-/
@[specialize] def zipWith (f : α → β → γ) : (xs : List α) → (ys : List β) → List γ
  | x::xs, y::ys => f x y :: zipWith f xs ys
  | _,     _     => []

/--
`O(min |xs| |ys|)`. Combines the two lists into a list of pairs, with one element from each list.
The longer list is truncated to match the shorter list.
* `zip [x₁, x₂, x₃] [y₁, y₂, y₃, y₄] = [(x₁, y₁), (x₂, y₂), (x₃, y₃)]`
-/
def zip : List α → List β → List (Prod α β) :=
  zipWith Prod.mk

/--
`O(|l|)`. Separates a list of pairs into two lists containing the first components and second components.
* `unzip [(x₁, y₁), (x₂, y₂), (x₃, y₃)] = ([x₁, x₂, x₃], [y₁, y₂, y₃])`
-/
def unzip : List (α × β) → List α × List β
  | []          => ([], [])
  | (a, b) :: t => match unzip t with | (al, bl) => (a::al, b::bl)

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

/--
`O(n)`. `iota n` is the numbers from `1` to `n` inclusive, in decreasing order.
* `iota 5 = [5, 4, 3, 2, 1]`
-/
def iota : Nat → List Nat
  | 0       => []
  | m@(n+1) => m :: iota n

/-- Tail-recursive version of `iota`. -/
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

/--
`O(|l|)`. `enumFrom n l` is like `enum` but it allows you to specify the initial index.
* `enumFrom 5 [a, b, c] = [(5, a), (6, b), (7, c)]`
-/
def enumFrom : Nat → List α → List (Nat × α)
  | _, [] => nil
  | n, x :: xs   => (n, x) :: enumFrom (n + 1) xs

/--
`O(|l|)`. `enum l` pairs up each element with its index in the list.
* `enum [a, b, c] = [(0, a), (1, b), (2, c)]`
-/
def enum : List α → List (Nat × α) := enumFrom 0

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

/--
`O(|xs|)`. `intercalate sep xs` alternates `sep` and the elements of `xs`:
* `intercalate sep [] = []`
* `intercalate sep [a] = a`
* `intercalate sep [a, b] = a ++ sep ++ b`
* `intercalate sep [a, b, c] = a ++ sep ++ b ++ sep ++ c`
-/
def intercalate (sep : List α) (xs : List (List α)) : List α :=
  join (intersperse sep xs)

/--
`bind xs f` is the bind operation of the list monad. It applies `f` to each element of `xs`
to get a list of lists, and then concatenates them all together.
* `[2, 3, 2].bind range = [0, 1, 0, 1, 2, 0, 1]`
-/
@[inline] protected def bind {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β := join (map b a)

/-- `pure x = [x]` is the `pure` operation of the list monad. -/
@[inline] protected def pure {α : Type u} (a : α) : List α := [a]

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

instance hasDecidableLt [LT α] [h : DecidableRel (α:=α) (·<·)] : (l₁ l₂ : List α) → Decidable (l₁ < l₂)
  | [],    []    => isFalse (fun h => nomatch h)
  | [],    _::_  => isTrue (List.lt.nil _ _)
  | _::_, []     => isFalse (fun h => nomatch h)
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

/--  `isPrefixOf l₁ l₂` returns `true` Iff `l₁` is a prefix of `l₂`.
That is, there exists a `t` such that `l₂ == l₁ ++ t`. -/
def isPrefixOf [BEq α] : List α → List α → Bool
  | [],    _     => true
  | _,     []    => false
  | a::as, b::bs => a == b && isPrefixOf as bs

/-- `isPrefixOf? l₁ l₂` returns `some t` when `l₂ == l₁ ++ t`. -/
def isPrefixOf? [BEq α] : List α → List α → Option (List α)
  | [], l₂ => some l₂
  | _, [] => none
  | (x₁ :: l₁), (x₂ :: l₂) =>
    if x₁ == x₂ then isPrefixOf? l₁ l₂ else none

/--  `isSuffixOf l₁ l₂` returns `true` Iff `l₁` is a suffix of `l₂`.
That is, there exists a `t` such that `l₂ == t ++ l₁`. -/
def isSuffixOf [BEq α] (l₁ l₂ : List α) : Bool :=
  isPrefixOf l₁.reverse l₂.reverse

/-- `isSuffixOf? l₁ l₂` returns `some t` when `l₂ == t ++ l₁`.-/
def isSuffixOf? [BEq α] (l₁ l₂ : List α) : Option (List α) :=
  Option.map List.reverse <| isPrefixOf? l₁.reverse l₂.reverse

/--
`O(min |as| |bs|)`. Returns true if `as` and `bs` have the same length,
and they are pairwise related by `eqv`.
-/
@[specialize] def isEqv : (as bs : List α) → (eqv : α → α → Bool) → Bool
  | [],    [],    _   => true
  | a::as, b::bs, eqv => eqv a b && isEqv as bs eqv
  | _,     _,     _   => false

/--
The equality relation on lists asserts that they have the same length
and they are pairwise `BEq`.
-/
protected def beq [BEq α] : List α → List α → Bool
  | [],    []    => true
  | a::as, b::bs => a == b && List.beq as bs
  | _,     _     => false

instance [BEq α] : BEq (List α) := ⟨List.beq⟩

/--
`replicate n a` is `n` copies of `a`:
* `replicate 5 a = [a, a, a, a, a]`
-/
@[simp] def replicate : (n : Nat) → (a : α) → List α
  | 0,   _ => []
  | n+1, a => a :: replicate n a

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

@[csimp] theorem replicate_eq_replicateTR : @List.replicate = @List.replicateTR := by
  apply funext; intro α; apply funext; intro n; apply funext; intro a
  exact (replicateTR_loop_replicate_eq _ 0 n).symm

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

@[simp] theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  induction n <;> simp_all

@[simp] theorem length_concat (as : List α) (a : α) : (concat as a).length = as.length + 1 := by
  induction as with
  | nil => rfl
  | cons _ xs ih => simp [concat, ih]

@[simp] theorem length_set (as : List α) (i : Nat) (a : α) : (as.set i a).length = as.length := by
  induction as generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [set, ih]

@[simp] theorem length_dropLast_cons (a : α) (as : List α) : (a :: as).dropLast.length = as.length := by
  match as with
  | []       => rfl
  | b::bs =>
    have ih := length_dropLast_cons b bs
    simp[dropLast, ih]

@[simp] theorem length_append (as bs : List α) : (as ++ bs).length = as.length + bs.length := by
  induction as with
  | nil => simp
  | cons _ as ih => simp [ih, Nat.succ_add]

@[simp] theorem length_map (as : List α) (f : α → β) : (as.map f).length = as.length := by
  induction as with
  | nil => simp [List.map]
  | cons _ as ih => simp [List.map, ih]

@[simp] theorem length_reverse (as : List α) : (as.reverse).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

/--
Returns the largest element of the list, if it is not empty.
* `[].maximum? = none`
* `[4].maximum? = some 4`
* `[1, 4, 2, 10, 6].maximum? = some 10`
-/
def maximum? [Max α] : List α → Option α
  | []    => none
  | a::as => some <| as.foldl max a

/--
Returns the smallest element of the list, if it is not empty.
* `[].minimum? = none`
* `[4].minimum? = some 4`
* `[1, 4, 2, 10, 6].minimum? = some 1`
-/
def minimum? [Min α] : List α → Option α
  | []    => none
  | a::as => some <| as.foldl min a

instance [BEq α] [LawfulBEq α] : LawfulBEq (List α) where
  eq_of_beq {as bs} := by
    induction as generalizing bs with
    | nil => intro h; cases bs <;> first | rfl | contradiction
    | cons a as ih =>
      cases bs with
      | nil => intro h; contradiction
      | cons b bs =>
        simp [show (a::as == b::bs) = (a == b && as == bs) from rfl]
        intro ⟨h₁, h₂⟩
        exact ⟨h₁, ih h₂⟩
  rfl {as} := by
    induction as with
    | nil => rfl
    | cons a as ih => simp [BEq.beq, List.beq, LawfulBEq.rfl]; exact ih

theorem of_concat_eq_concat {as bs : List α} {a b : α} (h : as.concat a = bs.concat b) : as = bs ∧ a = b := by
  match as, bs with
  | [], [] => simp [concat] at h; simp [h]
  | [_], [] => simp [concat] at h
  | _::_::_, [] => simp [concat] at h
  | [], [_] => simp [concat] at h
  | [], _::_::_ => simp [concat] at h
  | _::_, _::_ => simp [concat] at h; simp [h]; apply of_concat_eq_concat h.2

theorem concat_eq_append (as : List α) (a : α) : as.concat a = as ++ [a] := by
  induction as <;> simp [concat, *]

theorem drop_eq_nil_of_le {as : List α} {i : Nat} (h : as.length ≤ i) : as.drop i = [] := by
  match as, i with
  | [],    i   => simp
  | _::_,  0   => simp at h
  | _::as, i+1 => simp at h; exact @drop_eq_nil_of_le as i (Nat.le_of_succ_le_succ h)

end List
