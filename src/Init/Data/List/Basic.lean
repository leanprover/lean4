/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Data.List.Notation
public import Init.Data.Zero
public import Init.Grind.Tactics
public import Init.SimpLemmas
import Init.Data.Nat.Basic

public section

@[expose] section

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
* Ranges and enumeration: `range`, `zipIdx`.
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
set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

open Decidable List

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

/-! ## Preliminaries from `Init.Prelude` -/

/-! ### length -/

@[simp, grind =] theorem length_nil : length ([] : List α) = 0 :=
  rfl

@[simp] theorem length_singleton {a : α} : length [a] = 1 := rfl

@[simp, grind =] theorem length_cons {a : α} {as : List α} : (cons a as).length = as.length + 1 :=
  rfl

/-! ### set -/

@[simp, grind =] theorem length_set {as : List α} {i : Nat} {a : α} : (as.set i a).length = as.length := by
  induction as generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [set, ih]

/-! ### foldl -/

-- As `List.foldl` is defined in `Init.Prelude`, we write the basic simplification lemmas here.
@[simp, grind =] theorem foldl_nil : [].foldl f b = b := rfl
@[simp, grind =] theorem foldl_cons {l : List α} {f : β → α → β} {b : β} : (a :: l).foldl f b = l.foldl f (f b a) := rfl

/-! ### concat -/

theorem length_concat {as : List α} {a : α} : (concat as a).length = as.length + 1 := by
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
Checks whether two lists have the same length and their elements are pairwise `BEq`. Normally used
via the `==` operator.
-/
protected def beq [BEq α] : List α → List α → Bool
  | [],    []    => true
  | a::as, b::bs => a == b && List.beq as bs
  | _,     _     => false

@[simp] theorem beq_nil_nil [BEq α] : List.beq ([] : List α) ([] : List α) = true := rfl
@[simp] theorem beq_cons_nil [BEq α] {a : α} {as : List α} : List.beq (a::as) [] = false := rfl
@[simp] theorem beq_nil_cons [BEq α] {a : α} {as : List α} : List.beq [] (a::as) = false := rfl
theorem beq_cons_cons [BEq α] {a b : α} {as bs : List α} : List.beq (a::as) (b::bs) = (a == b && List.beq as bs) := rfl

@[deprecated beq_cons_cons (since := "2026-02-26")]
theorem beq_cons₂ [BEq α] {a b : α} {as bs : List α} :
    List.beq (a::as) (b::bs) = (a == b && List.beq as bs) := beq_cons_cons

instance [BEq α] : BEq (List α) := ⟨List.beq⟩

instance [BEq α] [ReflBEq α] : ReflBEq (List α) where
  rfl {as} := by
    induction as with
    | nil => rfl
    | cons a as ih => simp [BEq.beq, List.beq]; exact ih

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

/--
Returns `true` if `as` and `bs` have the same length and they are pairwise related by `eqv`.

`O(min |as| |bs|)`. Short-circuits at the first non-related pair of elements.

Examples:
* `[1, 2, 3].isEqv [2, 3, 4] (· < ·) = true`
* `[1, 2, 3].isEqv [2, 2, 4] (· < ·) = false`
* `[1, 2, 3].isEqv [2, 3] (· < ·) = false`
-/
@[specialize] def isEqv : (as bs : List α) → (eqv : α → α → Bool) → Bool
  | [],    [],    _   => true
  | a::as, b::bs, eqv => eqv a b && isEqv as bs eqv
  | _,     _,     _   => false

@[simp, grind =] theorem isEqv_nil_nil : isEqv ([] : List α) [] eqv = true := rfl
@[simp, grind =] theorem isEqv_nil_cons : isEqv ([] : List α) (a::as) eqv = false := rfl
@[simp, grind =] theorem isEqv_cons_nil : isEqv (a::as : List α) [] eqv = false := rfl
@[grind =] theorem isEqv_cons_cons : isEqv (a::as) (b::bs) eqv = (eqv a b && isEqv as bs eqv) := rfl

@[deprecated isEqv_cons_cons (since := "2026-02-26")]
theorem isEqv_cons₂ : isEqv (a::as) (b::bs) eqv = (eqv a b && isEqv as bs eqv) := isEqv_cons_cons


/-! ## Lexicographic ordering -/

/--
Lexicographic ordering for lists with respect to an ordering of elements.

`as` is lexicographically smaller than `bs` if
 * `as` is empty and `bs` is non-empty, or
 * both `as` and `bs` are non-empty, and the head of `as` is less than the head of `bs` according to
   `r`, or
 * both `as` and `bs` are non-empty, their heads are equal, and the tail of `as` is less than the
   tail of `bs`.
-/
inductive Lex (r : α → α → Prop) : (as : List α) → (bs : List α) → Prop
  /-- `[]` is the smallest element in the lexicographic order. -/
  | nil {a l} : Lex r [] (a :: l)
  /--
  If the head of the first list is smaller than the head of the second, then the first list is
  lexicographically smaller than the second list.
  -/
  | rel {a₁ l₁ a₂ l₂} (h : r a₁ a₂) : Lex r (a₁ :: l₁) (a₂ :: l₂)
  /--
  If two lists have the same head, then their tails determine their lexicographic order. If the tail
  of the first list is lexicographically smaller than the tail of the second list, then the entire
  first list is lexicographically smaller than the entire second list.
  -/
  | cons {a l₁ l₂} (h : Lex r l₁ l₂) : Lex r (a :: l₁) (a :: l₂)


instance decidableLex [DecidableEq α] (r : α → α → Prop) [h : DecidableRel r] :
    (l₁ l₂ : List α) → Decidable (Lex r l₁ l₂)
  | [], [] => isFalse nofun
  | [], _::_ => isTrue Lex.nil
  | _::_, [] => isFalse nofun
  | a::as, b::bs =>
    match h a b with
    | isTrue h₁ => isTrue (Lex.rel h₁)
    | isFalse h₁ =>
      if h₂ : a = b then
        match decidableLex r as bs with
        | isTrue h₃ => isTrue (h₂ ▸ Lex.cons h₃)
        | isFalse h₃ => isFalse (fun h => match h with
          | Lex.rel h₁' => absurd h₁' h₁
          | Lex.cons h₃' => absurd h₃' h₃)
      else
        isFalse (fun h => match h with
          | Lex.rel h₁' => absurd h₁' h₁
          | Lex.cons h₂' => h₂ rfl)

/--
Lexicographic ordering of lists with respect to an ordering on their elements.

`as < bs` if
 * `as` is empty and `bs` is non-empty, or
 * both `as` and `bs` are non-empty, and the head of `as` is less than the head of `bs`, or
 * both `as` and `bs` are non-empty, their heads are equal, and the tail of `as` is less than the
   tail of `bs`.
-/
protected abbrev lt [LT α] : List α → List α → Prop := Lex (· < ·)

instance instLT [LT α] : LT (List α) := ⟨List.lt⟩

/-- Decidability of lexicographic ordering. -/
instance decidableLT [DecidableEq α] [LT α] [DecidableLT α] (l₁ l₂ : List α) :
    Decidable (l₁ < l₂) := decidableLex (· < ·) l₁ l₂



/--
Non-strict ordering of lists with respect to a strict ordering of their elements.

`as ≤ bs` if `¬ bs < as`.

This relation can be treated as a lexicographic order if the underlying `LT α` instance is
well-behaved. In particular, it should be irreflexive, asymmetric, and antisymmetric. These
requirements are precisely formulated in `List.cons_le_cons_iff`. If these hold, then `as ≤ bs` if
and only if:
 * `as` is empty, or
 * both `as` and `bs` are non-empty, and the head of `as` is less than the head of `bs`, or
 * both `as` and `bs` are non-empty, their heads are equal, and the tail of `as` is less than or
   equal to the tail of `bs`.
-/
@[reducible] protected def le [LT α] (as bs : List α) : Prop := ¬ bs < as

instance instLE [LT α] : LE (List α) := ⟨List.le⟩

instance decidableLE [DecidableEq α] [LT α] [DecidableLT α] (l₁ l₂ : List α) :
    Decidable (l₁ ≤ l₂) :=
  inferInstanceAs (Decidable (Not _))

/--
Compares lists lexicographically with respect to a comparison on their elements.

The lexicographic order with respect to `lt` is:
* `[].lex (b :: bs)` is `true`
* `as.lex [] = false` is `false`
* `(a :: as).lex (b :: bs)` is true if `lt a b` or `a == b` and `lex lt as bs` is true.
-/
def lex [BEq α] (l₁ l₂ : List α) (lt : α → α → Bool := by exact (· < ·)) : Bool :=
  match l₁, l₂ with
  | [],      _ :: _  => true
  | _,      []       => false
  | a :: as, b :: bs => lt a b || (a == b && lex as bs lt)

theorem nil_lex_nil [BEq α] : lex ([] : List α) [] lt = false := rfl
@[simp] theorem nil_lex_cons [BEq α] {b} {bs : List α} : lex [] (b :: bs) lt = true := rfl
theorem cons_lex_nil [BEq α] {a} {as : List α} : lex (a :: as) [] lt = false := rfl
@[simp] theorem cons_lex_cons [BEq α] {a b} {as bs : List α} :
    lex (a :: as) (b :: bs) lt = (lt a b || (a == b && lex as bs lt)) := rfl

@[simp] theorem lex_nil [BEq α] {as : List α} : lex as [] lt = false := by
  cases as <;> simp [nil_lex_nil, cons_lex_nil]

/-! ## Alternative getters -/

/-! ### getLast -/

/--
Returns the last element of a non-empty list.

Examples:
 * `["circle", "rectangle"].getLast (by decide) = "rectangle"`
 * `["circle"].getLast (by decide) = "circle"`
-/
def getLast : ∀ (as : List α), as ≠ [] → α
  | [],       h => absurd rfl h
  | [a],      _ => a
  | _::b::as, _ => getLast (b::as) (fun h => List.noConfusion rfl (heq_of_eq h))

/-! ### getLast? -/

/--
Returns the last element in the list, or `none` if the list is empty.

Alternatives include `List.getLastD`, which takes a fallback value for empty lists, and
`List.getLast!`, which panics on empty lists.

Examples:
 * `["circle", "rectangle"].getLast? = some "rectangle"`
 * `["circle"].getLast? = some "circle"`
 * `([] : List String).getLast? = none`
-/
def getLast? : List α → Option α
  | []    => none
  | a::as => some (getLast (a::as) (fun h => List.noConfusion rfl (heq_of_eq h)))

@[simp, grind =] theorem getLast?_nil : @getLast? α [] = none := rfl

/-! ### getLastD -/

/--
Returns the last element in the list, or `fallback` if the list is empty.

Alternatives include `List.getLast?`, which returns an `Option`, and `List.getLast!`, which panics
on empty lists.

Examples:
 * `["circle", "rectangle"].getLastD "oval" = "rectangle"`
 * `["circle"].getLastD "oval" = "circle"`
 * `([] : List String).getLastD "oval" = "oval"`
-/
def getLastD : (as : List α) → (fallback : α) → α
  | [],   a₀ => a₀
  | a::as, _ => getLast (a::as) (fun h => List.noConfusion rfl (heq_of_eq h))

-- These aren't `simp` lemmas since we always simplify `getLastD` in terms of `getLast?`.
theorem getLastD_nil {a : α} : getLastD [] a = a := rfl
theorem getLastD_cons {a b : α} {l} : getLastD (b::l) a = getLastD l b := by cases l <;> rfl

/-! ## Head and tail -/

/-! ### head -/

/--
Returns the first element of a non-empty list.
-/
def head : (as : List α) → as ≠ [] → α
  | a::_, _ => a

@[simp, grind =] theorem head_cons {a : α} {l : List α} {h} : head (a::l) h = a := rfl

/-! ### head? -/

/--
Returns the first element in the list, if there is one. Returns `none` if the list is empty.

Use `List.headD` to provide a fallback value for empty lists, or `List.head!` to panic on empty
lists.

Examples:
 * `([] : List Nat).head? = none`
 * `[3, 2, 1].head? = some 3`
-/
def head? : List α → Option α
  | []   => none
  | a::_ => some a

@[simp, grind =] theorem head?_nil : head? ([] : List α) = none := rfl
@[simp, grind =] theorem head?_cons {a : α} {l : List α} : head? (a::l) = some a := rfl

/-! ### headD -/

/--
Returns the first element in the list if there is one, or `fallback` if the list is empty.

Use `List.head?` to return an `Option`, and `List.head!` to panic on empty lists.

Examples:
 * `[].headD "empty" = "empty"`
 * `[].headD 2 = 2`
 * `["head", "shoulders", "knees"].headD "toes" = "head"`
-/
def headD : (as : List α) → (fallback : α) → α
  | [],   fallback => fallback
  | a::_, _  => a

@[simp] theorem headD_nil {d : α} : headD [] d = d := rfl
@[simp] theorem headD_cons {a : α} {l : List α} {d : α} : headD (a::l) d = a := rfl

/-! ### tail -/

/--
Drops the first element of a nonempty list, returning the tail. Returns `[]` when the argument is
empty.

Examples:
 * `["apple", "banana", "grape"].tail = ["banana", "grape"]`
 * `["apple"].tail = []`
 * `([] : List String).tail = []`
-/
def tail : List α → List α
  | []    => []
  | _::as => as

@[simp, grind =] theorem tail_nil : tail ([] : List α) = [] := rfl
@[simp, grind =] theorem tail_cons {a : α} {as : List α} : tail (a::as) = as := rfl

/-! ### tail? -/

/--
Drops the first element of a nonempty list, returning the tail. Returns `none` when the argument is
empty.

Alternatives include `List.tail`, which returns the empty list on failure, `List.tailD`, which
returns an explicit fallback value, and `List.tail!`, which panics on the empty list.

Examples:
 * `["apple", "banana", "grape"].tail? = some ["banana", "grape"]`
 * `["apple"].tail? = some []`
 * `([] : List String).tail = none`
-/
def tail? : List α → Option (List α)
  | []    => none
  | _::as => some as

@[simp, grind =] theorem tail?_nil : tail? ([] : List α) = none := rfl
@[simp, grind =] theorem tail?_cons {a : α} {l : List α} : tail? (a::l) = some l := rfl

/-! ### tailD -/

set_option linter.listVariables false in
/--
Drops the first element of a nonempty list, returning the tail. Returns `none` when the argument is
empty.

Alternatives include `List.tail`, which returns the empty list on failure, `List.tail?`, which
returns an `Option`, and `List.tail!`, which panics on the empty list.

Examples:
 * `["apple", "banana", "grape"].tailD ["orange"] = ["banana", "grape"]`
 * `["apple"].tailD ["orange"] = []`
 * `[].tailD ["orange"] = ["orange"]`
-/
def tailD (l fallback : List α) : List α :=
  match l with
  | [] => fallback
  | _ :: tl => tl

@[simp] theorem tailD_nil {l' : List α} : tailD [] l' = l' := rfl
@[simp] theorem tailD_cons {a : α} {l : List α} {l' : List α} : tailD (a::l) l' = l := rfl

/-! ## Basic `List` operations.

We define the basic functional programming operations on `List`:
`map`, `filter`, `filterMap`, `foldr`, `append`, `flatten`, `pure`, `bind`, `replicate`, and `reverse`.
-/

/-! ### map -/

@[simp, grind =] theorem map_nil {f : α → β} : map f [] = [] := rfl
@[simp, grind =] theorem map_cons {f : α → β} {a : α} {l : List α} : map f (a :: l) = f a :: map f l := rfl

/-! ### filter -/

/--
Returns the list of elements in `l` for which `p` returns `true`.

`O(|l|)`.

Examples:
* `[1, 2, 5, 2, 7, 7].filter (· > 2) = [5, 7, 7]`
* `[1, 2, 5, 2, 7, 7].filter (fun _ => false) = []`
* `[1, 2, 5, 2, 7, 7].filter (fun _ => true) = [1, 2, 5, 2, 7, 7]`
-/
def filter (p : α → Bool) : (l : List α) → List α
  | [] => []
  | a::as => match p a with
    | true => a :: filter p as
    | false => filter p as

@[simp, grind =] theorem filter_nil {p : α → Bool} : filter p [] = [] := rfl

/-! ### filterMap -/

/--
Applies a function that returns an `Option` to each element of a list, collecting the non-`none`
values.

`O(|l|)`.

Example:
```lean example
#eval [1, 2, 5, 2, 7, 7].filterMap fun x =>
  if x > 2 then some (2 * x) else none
```
```output
[10, 14, 14]
```
-/
noncomputable def filterMap (f : α → Option β) : List α → List β
  | []   => []
  | a::as =>
    match f a with
    | none   => filterMap f as
    | some b => b :: filterMap f as

@[simp, grind =] theorem filterMap_nil {f : α → Option β} : filterMap f [] = [] := rfl
@[grind =] theorem filterMap_cons {f : α → Option β} {a : α} {l : List α} :
    filterMap f (a :: l) =
      match f a with
      | none => filterMap f l
      | some b => b :: filterMap f l := rfl

/-! ### foldr -/

/--
Folds a function over a list from the right, accumulating a value starting with `init`. The
accumulated value is combined with the each element of the list in reverse order, using `f`.

`O(|l|)`. Replaced at runtime with `List.foldrTR`.

Examples:
 * `[a, b, c].foldr f init  = f a (f b (f c init))`
 * `[1, 2, 3].foldr (toString · ++ ·) "" = "123"`
 * `[1, 2, 3].foldr (s!"({·} {·})") "!" = "(1 (2 (3 !)))"`
-/
@[specialize] def foldr (f : α → β → β) (init : β) : (l : List α) → β
  | []     => init
  | a :: l => f a (foldr f init l)

@[simp, grind =] theorem foldr_nil : [].foldr f b = b := rfl
@[simp, grind =] theorem foldr_cons {a} {l : List α} {f : α → β → β} {b} :
    (a :: l).foldr f b = f a (l.foldr f b) := rfl

/-! ### reverse -/

/-- Auxiliary for `List.reverse`. `List.reverseAux l r = l.reverse ++ r`, but it is defined directly. -/
def reverseAux : List α → List α → List α
  | [],   r => r
  | a::l, r => reverseAux l (a::r)

@[simp] theorem reverseAux_nil : reverseAux [] r = r := rfl
@[simp] theorem reverseAux_cons : reverseAux (a::l) r = reverseAux l (a::r) := rfl

/--
Reverses a list.

`O(|as|)`.

Because of the “functional but in place” optimization implemented by Lean's compiler, this function
does not allocate a new list when its reference to the input list is unshared: it simply walks the
linked list and reverses all the node pointers.

Examples:
* `[1, 2, 3, 4].reverse = [4, 3, 2, 1]`
* `[].reverse = []`
-/
@[expose] def reverse (as : List α) : List α :=
  reverseAux as []

@[simp, grind =] theorem reverse_nil : reverse ([] : List α) = [] := rfl

theorem reverseAux_reverseAux {as bs cs : List α} :
    reverseAux (reverseAux as bs) cs = reverseAux bs (reverseAux (reverseAux as []) cs) := by
  induction as generalizing bs cs with
  | nil => rfl
  | cons a as ih => simp [reverseAux, ih (bs := a::bs), ih (bs := [a])]

/-! ### append -/

/--
Appends two lists. Normally used via the `++` operator.

Appending lists takes time proportional to the length of the first list: `O(|xs|)`.

This is a tail-recursive version of `List.append`.

Examples:
  * `[1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5]`.
  * `[] ++ [4, 5] = [4, 5]`.
  * `[1, 2, 3] ++ [] = [1, 2, 3]`.
-/
-- The @[csimp] lemma for `appendTR` must be set up immediately, because otherwise `Append (List α)`
-- instance below will not use it.
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

@[simp] theorem append_eq {as bs : List α} : List.append as bs = as ++ bs := rfl

@[simp, grind =] theorem nil_append (as : List α) : [] ++ as = as := rfl
@[simp, grind _=_] theorem cons_append {a : α} {as bs : List α} : (a::as) ++ bs = a::(as ++ bs) := rfl

@[simp, grind =] theorem append_nil (as : List α) : as ++ [] = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp_all only [HAppend.hAppend, Append.append, List.append]

instance : Std.LawfulIdentity (α := List α) (· ++ ·) [] where
  left_id := nil_append
  right_id := append_nil

@[simp, grind =] theorem length_append {as bs : List α} : (as ++ bs).length = as.length + bs.length := by
  induction as with
  | nil => simp
  | cons _ as ih => simp [ih, Nat.succ_add]

@[simp] theorem append_assoc (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

grind_pattern append_assoc => (as ++ bs) ++ cs where
  as =/= []; bs =/= []; cs =/= []

grind_pattern append_assoc => as ++ (bs ++ cs) where
  as =/= []; bs =/= []; cs =/= []

instance : Std.Associative (α := List α) (· ++ ·) := ⟨append_assoc⟩

-- Arguments are explicit as there is often ambiguity inferring the arguments.
theorem append_cons (as : List α) (b : α) (bs : List α) : as ++ b :: bs = as ++ [b] ++ bs := by
  simp

@[simp, grind =] theorem concat_eq_append {as : List α} {a : α} : as.concat a = as ++ [a] := by
  induction as <;> simp [concat, *]

theorem reverseAux_eq_append {as bs : List α} : reverseAux as bs = reverseAux as [] ++ bs := by
  induction as generalizing bs with
  | nil => simp [reverseAux]
  | cons a as ih =>
    simp [reverseAux]
    rw [ih (bs := a :: bs), ih (bs := [a]), append_assoc]
    rfl

@[simp, grind =] theorem reverse_cons {a : α} {as : List α} : reverse (a :: as) = reverse as ++ [a] := by
  simp [reverse, reverseAux]
  rw [← reverseAux_eq_append]

/-! ### flatten -/


@[simp, grind =] theorem flatten_nil : List.flatten ([] : List (List α)) = [] := rfl
@[simp, grind =] theorem flatten_cons : (l :: L).flatten = l ++ L.flatten := rfl

/-! ### singleton -/

/--
Constructs a single-element list.

Examples:
 * `List.singleton 5 = [5]`.
 * `List.singleton "green" = ["green"]`.
 * `List.singleton [1, 2, 3] = [[1, 2, 3]]`
-/
@[inline, expose] protected def singleton {α : Type u} (a : α) : List α := [a]

/-! ### flatMap -/

@[simp, grind =] theorem flatMap_nil {f : α → List β} : List.flatMap f [] = [] := by simp [List.flatMap]
@[simp, grind =] theorem flatMap_cons {x : α} {xs : List α} {f : α → List β} :
  List.flatMap f (x :: xs) = f x ++ List.flatMap f xs := by simp [List.flatMap]

@[simp, grind _=_] theorem flatMap_append {xs ys : List α} {f : α → List β} :
    (xs ++ ys).flatMap f = xs.flatMap f ++ ys.flatMap f := by
  induction xs; {rfl}; simp_all [flatMap_cons, append_assoc]

/-! ### replicate -/

/--
Creates a list that contains `n` copies of `a`.

* `List.replicate 5 "five" = ["five", "five", "five", "five", "five"]`
* `List.replicate 0 "zero" = []`
* `List.replicate 2 ' ' = [' ', ' ']`
-/
def replicate : (n : Nat) → (a : α) → List α
  | 0,   _ => []
  | n+1, a => a :: replicate n a

@[simp, grind =] theorem replicate_zero {a : α} : replicate 0 a = [] := rfl
@[grind =] theorem replicate_succ {a : α} {n : Nat} : replicate (n+1) a = a :: replicate n a := rfl

@[simp, grind =] theorem length_replicate {n : Nat} {a : α} : (replicate n a).length = n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [ih, replicate_succ, length_cons]

/-! ## Additional functions -/

/-! ### leftpad and rightpad -/

/--
Pads `l : List α` on the left with repeated occurrences of `a : α` until it is of length `n`. If `l`
already has at least `n` elements, it is returned unmodified.

Examples:
 * `[1, 2, 3].leftpad 5 0 = [0, 0, 1, 2, 3]`
 * `["red", "green", "blue"].leftpad 4 "blank" = ["blank", "red", "green", "blue"]`
 * `["red", "green", "blue"].leftpad 3 "blank" = ["red", "green", "blue"]`
 * `["red", "green", "blue"].leftpad 1 "blank" = ["red", "green", "blue"]`
-/
@[simp, grind =]
def leftpad (n : Nat) (a : α) (l : List α) : List α := replicate (n - length l) a ++ l


/--
Pads `l : List α` on the right with repeated occurrences of `a : α` until it is of length `n`. If
`l` already has at least `n` elements, it is returned unmodified.

Examples:
 * `[1, 2, 3].rightpad 5 0 = [1, 2, 3, 0, 0]`
 * `["red", "green", "blue"].rightpad 4 "blank" = ["red", "green", "blue", "blank"]`
 * `["red", "green", "blue"].rightpad 3 "blank" = ["red", "green", "blue"]`
 * `["red", "green", "blue"].rightpad 1 "blank" = ["red", "green", "blue"]`
-/
@[simp, grind =]
def rightpad (n : Nat) (a : α) (l : List α) : List α := l ++ replicate (n - length l) a

/-! ## List membership

* `L.contains a : Bool` determines, using a `[BEq α]` instance, whether `L` contains an element `· == a`.
* `a ∈ L : Prop` is the proposition (only decidable if `α` has decidable equality) that `L` contains an element `· = a`.
-/

/-! ### EmptyCollection -/

instance : EmptyCollection (List α) := ⟨List.nil⟩

@[simp] theorem empty_eq : (∅ : List α) = [] := rfl

/-! ### isEmpty -/

/--
Checks whether a list is empty.

`O(1)`.

Examples:
* `[].isEmpty = true`
* `["grape"].isEmpty = false`
* `["apple", "banana"].isEmpty = false`
-/
def isEmpty : List α → Bool
  | []     => true
  | _ :: _ => false

@[simp, grind =] theorem isEmpty_nil : ([] : List α).isEmpty = true := rfl
@[simp, grind =] theorem isEmpty_cons : (x :: xs : List α).isEmpty = false := rfl

/-! ### elem -/

/--
Checks whether `a` is an element of `l`, using `==` to compare elements.

`O(|l|)`. `List.contains` is a synonym that takes the list before the element.

The preferred simp normal form is `l.contains a`. When `LawfulBEq α` is available,
`l.contains a = true ↔ a ∈ l` and `l.contains a = false ↔ a ∉ l`.

Example:
* `List.elem 3 [1, 4, 2, 3, 3, 7] = true`
* `List.elem 5 [1, 4, 2, 3, 3, 7] = false`
-/
def elem [BEq α] (a : α) : (l : List α) → Bool
  | []    => false
  | b::bs => match a == b with
    | true  => true
    | false => elem a bs

@[simp, grind =] theorem elem_nil [BEq α] : ([] : List α).elem a = false := rfl
theorem elem_cons [BEq α] {a : α} :
    (b::bs).elem a = match a == b with | true => true | false => bs.elem a := rfl

/-! ### contains -/

/--
Checks whether `a` is an element of `as`, using `==` to compare elements.

`O(|as|)`. `List.elem` is a synonym that takes the element before the list.

The preferred simp normal form is `l.contains a`, and when `LawfulBEq α` is available,
`l.contains a = true ↔ a ∈ l` and `l.contains a = false ↔ a ∉ l`.

Examples:
* `[1, 4, 2, 3, 3, 7].contains 3 = true`
* `List.contains [1, 4, 2, 3, 3, 7] 5 = false`
-/
abbrev contains [BEq α] (as : List α) (a : α) : Bool :=
  elem a as

@[simp] theorem contains_nil [BEq α] : ([] : List α).contains a = false := rfl

/-! ### Mem -/

/--
List membership, typically accessed via the `∈` operator.

`a ∈ l` means that `a` is an element of the list `l`. Elements are compared according to Lean's
logical equality.

The related function `List.elem` is a Boolean membership test that uses a `BEq α` instance.

Examples:
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
    next h => intros; simp at h; subst h; apply Mem.head
    next _ => intro h; exact Mem.tail _ (mem_of_elem_eq_true h)

theorem elem_eq_true_of_mem [BEq α] [ReflBEq α] {a : α} {as : List α} (h : a ∈ as) : elem a as = true := by
  induction h with
  | head _ => simp [elem]
  | tail _ _ ih => simp only [elem]; split; rfl; assumption

instance [BEq α] [LawfulBEq α] (a : α) (as : List α) : Decidable (a ∈ as) :=
  decidable_of_decidable_of_iff (Iff.intro mem_of_elem_eq_true elem_eq_true_of_mem)

theorem mem_append_left {a : α} {as : List α} (bs : List α) : a ∈ as → a ∈ as ++ bs := by
  intro h
  induction h with
  | head => apply Mem.head
  | tail => apply Mem.tail; assumption

theorem mem_append_right {b : α} (as : List α) {bs : List α} : b ∈ bs → b ∈ as ++ bs := by
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
Extracts the first `n` elements of `xs`, or the whole list if `n` is greater than `xs.length`.

`O(min n |xs|)`.

Examples:
* `[a, b, c, d, e].take 0 = []`
* `[a, b, c, d, e].take 3 = [a, b, c]`
* `[a, b, c, d, e].take 6 = [a, b, c, d, e]`
-/
def take : (n : Nat) → (xs : List α) → List α
  | 0,   _     => []
  | _+1, []    => []
  | n+1, a::as => a :: take n as

@[simp, grind =] theorem take_nil {i : Nat} : ([] : List α).take i = [] := by cases i <;> rfl
@[simp, grind =] theorem take_zero {l : List α} : l.take 0 = [] := rfl
@[simp, grind =] theorem take_succ_cons {a : α} {as : List α} {i : Nat} :
    (a::as).take (i+1) = a :: as.take i := rfl

/-! ### drop -/

/--
Removes the first `n` elements of the list `xs`. Returns the empty list if `n` is greater than the
length of the list.

`O(min n |xs|)`.

Examples:
* `[0, 1, 2, 3, 4].drop 0 = [0, 1, 2, 3, 4]`
* `[0, 1, 2, 3, 4].drop 3 = [3, 4]`
* `[0, 1, 2, 3, 4].drop 6 = []`
-/
def drop : (n : Nat) → (xs : List α) → List α
  | 0,   as     => as
  | _+1, []    => []
  | n+1, _::as => drop n as

@[simp, grind =] theorem drop_nil : ([] : List α).drop i = [] := by
  cases i <;> rfl
@[simp, grind =] theorem drop_zero {l : List α} : l.drop 0 = l := rfl
@[simp, grind =] theorem drop_succ_cons {a : α} {l : List α} {i : Nat} : (a :: l).drop (i + 1) = l.drop i := rfl

theorem drop_eq_nil_of_le {as : List α} {i : Nat} (h : as.length ≤ i) : as.drop i = [] := by
  match as, i with
  | [],    i   => simp
  | _::_,  0   => simp at h
  | _::as, i+1 => simp only [length_cons] at h; exact @drop_eq_nil_of_le as i (Nat.le_of_succ_le_succ h)

/-! ### extract -/

/--
Returns the slice of `l` from indices `start` (inclusive) to `stop` (exclusive).

Examples:
* [0, 1, 2, 3, 4, 5].extract 1 2 = [1]
* [0, 1, 2, 3, 4, 5].extract 2 2 = []
* [0, 1, 2, 3, 4, 5].extract 2 4 = [2, 3]
* [0, 1, 2, 3, 4, 5].extract 2 = [2, 3, 4, 5]
* [0, 1, 2, 3, 4, 5].extract (stop := 2) = [0, 1]
-/
-- This is only an abbreviation for the operation in terms of `drop` and `take`.
-- We do not prove properties of extract itself.
def extract (l : List α) (start : Nat := 0) (stop : Nat := l.length) : List α :=
  (l.drop start).take (stop - start)

theorem extract_eq_take_drop {l : List α} {start stop : Nat} :
    l.extract start stop = (l.drop start).take (stop - start) := rfl

set_option linter.missingDocs false in
@[deprecated extract_eq_take_drop (since := "2026-02-06")]
def extract_eq_drop_take := @extract_eq_take_drop

/-! ### takeWhile -/

/--
 Returns the longest initial segment of `xs` for which `p` returns true.

`O(|xs|)`.

Examples:
* `[7, 6, 4, 8].takeWhile (· > 5) = [7, 6]`
* `[7, 6, 6, 5].takeWhile (· > 5) = [7, 6, 6]`
* `[7, 6, 6, 8].takeWhile (· > 5) = [7, 6, 6, 8]`
-/
def takeWhile (p : α → Bool) : (xs : List α) → List α
  | []       => []
  | hd :: tl => match p hd with
   | true  => hd :: takeWhile p tl
   | false => []

@[simp] theorem takeWhile_nil : ([] : List α).takeWhile p = [] := rfl

/-! ### dropWhile -/

/--
Removes the longest prefix of a list for which `p` returns `true`.

Elements are removed from the list until one is encountered for which `p` returns `false`. This
element and the remainder of the list are returned.

`O(|l|)`.

Examples:
 * `[1, 3, 2, 4, 2, 7, 4].dropWhile (· < 4) = [4, 2, 7, 4]`
 * `[8, 3, 2, 4, 2, 7, 4].dropWhile (· < 4) = [8, 3, 2, 4, 2, 7, 4]`
 * `[8, 3, 2, 4, 2, 7, 4].dropWhile (· < 100) = []`
-/
def dropWhile (p : α → Bool) : List α → List α
  | []   => []
  | a::l => match p a with
    | true  => dropWhile p l
    | false => a::l

@[simp] theorem dropWhile_nil : ([] : List α).dropWhile p = [] := rfl

/-! ### partition -/

/--
Returns a pair of lists that together contain all the elements of `as`. The first list contains
those elements for which `p` returns `true`, and the second contains those for which `p` returns
`false`.

`O(|l|)`. `as.partition p` is equivalent to `(as.filter p, as.filter (not ∘ p))`, but it is slightly
more efficient since it only has to do one pass over the list.

Examples:
 * `[1, 2, 5, 2, 7, 7].partition (· > 2) = ([5, 7, 7], [1, 2, 2])`
 * `[1, 2, 5, 2, 7, 7].partition (fun _ => false) = ([], [1, 2, 5, 2, 7, 7])`
 * `[1, 2, 5, 2, 7, 7].partition (fun _ => true) = ([1, 2, 5, 2, 7, 7], [])`
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
Removes the last element of the list, if one exists.

Examples:
* `[].dropLast = []`
* `["tea"].dropLast = []`
* `["tea", "coffee", "juice"].dropLast = ["tea", "coffee"]`
-/
def dropLast {α} : List α → List α
  | []    => []
  | [_]   => []
  | a::as => a :: dropLast as

@[simp, grind =] theorem dropLast_nil : ([] : List α).dropLast = [] := rfl
@[simp, grind =] theorem dropLast_singleton : [x].dropLast = [] := rfl

@[simp, grind =] theorem dropLast_cons_cons :
    (x::y::zs).dropLast = x :: (y::zs).dropLast := rfl

@[deprecated dropLast_cons_cons (since := "2026-02-26")]
theorem dropLast_cons₂ : (x::y::zs).dropLast = x :: (y::zs).dropLast := dropLast_cons_cons

-- Later this can be proved by `simp` via `[List.length_dropLast, List.length_cons, Nat.add_sub_cancel]`,
-- but we need this while bootstrapping `Array`.
@[simp] theorem length_dropLast_cons {a : α} {as : List α} : (a :: as).dropLast.length = as.length := by
  match as with
  | []       => rfl
  | b::bs => simp [dropLast, length_dropLast_cons]

/-! ### Subset -/

/--
`l₁ ⊆ l₂` means that every element of `l₁` is also an element of `l₂`, ignoring multiplicity.
-/
protected def Subset (l₁ l₂ : List α) := ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂

instance : HasSubset (List α) := ⟨List.Subset⟩

instance [DecidableEq α] : DecidableRel (Subset : List α → List α → Prop) :=
  fun _ _ => decidableBAll _ _

/-! ### Sublist and isSublist -/

/--
The first list is a non-contiguous sub-list of the second list. Typically written with the `<+`
operator.

In other words, `l₁ <+ l₂` means that `l₁` can be transformed into `l₂` by repeatedly inserting new
elements.
-/
inductive Sublist {α} : List α → List α → Prop
  /-- The base case: `[]` is a sublist of `[]` -/
  | slnil : Sublist [] []
  /-- If `l₁` is a subsequence of `l₂`, then it is also a subsequence of `a :: l₂`. -/
  | cons a : Sublist l₁ l₂ → Sublist l₁ (a :: l₂)
  /-- If `l₁` is a subsequence of `l₂`, then `a :: l₁` is a subsequence of `a :: l₂`. -/
  | cons_cons a : Sublist l₁ l₂ → Sublist (a :: l₁) (a :: l₂)

set_option linter.missingDocs false in
@[deprecated Sublist.cons_cons (since := "2026-02-26"), match_pattern]
abbrev Sublist.cons₂ := @Sublist.cons_cons

@[inherit_doc] scoped infixl:50 " <+ " => Sublist

/--
True if the first list is a potentially non-contiguous sub-sequence of the second list, comparing
elements with the `==` operator.

The relation `List.Sublist` is a logical characterization of this property.

Examples:
* `[1, 3].isSublist [0, 1, 2, 3, 4] = true`
* `[1, 3].isSublist [0, 1, 2, 4] = false`
-/
def isSublist [BEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | l₁@(hd₁::tl₁), hd₂::tl₂ =>
    if hd₁ == hd₂
    then tl₁.isSublist tl₂
    else l₁.isSublist tl₂

/-! ### IsPrefix / isPrefixOf / isPrefixOf? -/

/--
The first list is a prefix of the second.

`IsPrefix l₁ l₂`, written `l₁ <+: l₂`, means that there exists some `t : List α` such that `l₂` has
the form `l₁ ++ t`.

The function `List.isPrefixOf` is a Boolean equivalent.
-/
def IsPrefix (l₁ : List α) (l₂ : List α) : Prop := Exists fun t => l₁ ++ t = l₂

@[inherit_doc] infixl:50 " <+: " => IsPrefix

/-- not `isPrefix` -/
recommended_spelling "prefix" for "<+:" in [IsPrefix, «term_<+:_»]

/--
Checks whether the first list is a prefix of the second.

The relation `List.IsPrefixOf` expresses this property with respect to logical equality.

Examples:
 * `[1, 2].isPrefixOf [1, 2, 3] = true`
 * `[1, 2].isPrefixOf [1, 2] = true`
 * `[1, 2].isPrefixOf [1] = false`
 * `[1, 2].isPrefixOf [1, 1, 2, 3] = false`
-/
def isPrefixOf [BEq α] : List α → List α → Bool
  | [],    _     => true
  | _,     []    => false
  | a::as, b::bs => a == b && isPrefixOf as bs

@[simp, grind =] theorem isPrefixOf_nil_left [BEq α] : isPrefixOf ([] : List α) l = true := by
  simp [isPrefixOf]
@[simp, grind =] theorem isPrefixOf_cons_nil [BEq α] : isPrefixOf (a::as) ([] : List α) = false := rfl
@[grind =] theorem isPrefixOf_cons_cons [BEq α] {a : α} :
    isPrefixOf (a::as) (b::bs) = (a == b && isPrefixOf as bs) := rfl

@[deprecated isPrefixOf_cons_cons (since := "2026-02-26")]
theorem isPrefixOf_cons₂ [BEq α] {a : α} :
    isPrefixOf (a::as) (b::bs) = (a == b && isPrefixOf as bs) := isPrefixOf_cons_cons

/--
If the first list is a prefix of the second, returns the result of dropping the prefix.

In other words, `isPrefixOf? l₁ l₂` returns `some t` when `l₂ == l₁ ++ t`.

Examples:
 * `[1, 2].isPrefixOf? [1, 2, 3] = some [3]`
 * `[1, 2].isPrefixOf? [1, 2] = some []`
 * `[1, 2].isPrefixOf? [1] = none`
 * `[1, 2].isPrefixOf? [1, 1, 2, 3] = none`
-/
def isPrefixOf? [BEq α] : (l₁ : List α) → (l₂ : List α) → Option (List α)
  | [], l₂ => some l₂
  | _, [] => none
  | (x₁ :: l₁), (x₂ :: l₂) =>
    if x₁ == x₂ then isPrefixOf? l₁ l₂ else none

/-! ### IsSuffix / isSuffixOf / isSuffixOf? -/

/--
Checks whether the first list is a suffix of the second.

The relation `List.IsSuffixOf` expresses this property with respect to logical equality.

Examples:
 * `[2, 3].isSuffixOf [1, 2, 3] = true`
 * `[2, 3].isSuffixOf [1, 2, 3, 4] = false`
 * `[2, 3].isSuffixOf [1, 2] = false`
 * `[2, 3].isSuffixOf [1, 1, 2, 3] = true`
-/
def isSuffixOf [BEq α] (l₁ l₂ : List α) : Bool :=
  isPrefixOf l₁.reverse l₂.reverse

@[simp, grind =] theorem isSuffixOf_nil_left [BEq α] : isSuffixOf ([] : List α) l = true := by
  simp [isSuffixOf]

/--
If the first list is a suffix of the second, returns the result of dropping the suffix from the
second.

In other words, `isSuffixOf? l₁ l₂` returns `some t` when `l₂ == t ++ l₁`.

Examples:
 * `[2, 3].isSuffixOf? [1, 2, 3] = some [1]`
 * `[2, 3].isSuffixOf? [1, 2, 3, 4] = none`
 * `[2, 3].isSuffixOf? [1, 2] = none`
 * `[2, 3].isSuffixOf? [1, 1, 2, 3] = some [1, 1]`
-/
def isSuffixOf? [BEq α] (l₁ l₂ : List α) : Option (List α) :=
  Option.map List.reverse <| isPrefixOf? l₁.reverse l₂.reverse

/--
The first list is a suffix of the second.

`IsSuffix l₁ l₂`, written `l₁ <:+ l₂`, means that there exists some `t : List α` such that `l₂` has
the form `t ++ l₁`.

The function `List.isSuffixOf` is a Boolean equivalent.
-/
def IsSuffix (l₁ : List α) (l₂ : List α) : Prop := Exists fun t => t ++ l₁ = l₂

@[inherit_doc] infixl:50 " <:+ " => IsSuffix

/-- not `isSuffix` -/
recommended_spelling "suffix" for "<:+" in [IsSuffix, «term_<:+_»]

/-! ### IsInfix -/

/--
The first list is a contiguous sub-list of the second list. Typically written with the `<:+:`
operator.

In other words, `l₁ <:+: l₂` means that there exist lists `s : List α` and `t : List α` such that
`l₂` has the form `s ++ l₁ ++ t`.
-/
def IsInfix (l₁ : List α) (l₂ : List α) : Prop := Exists fun s => Exists fun t => s ++ l₁ ++ t = l₂

@[inherit_doc] infixl:50 " <:+: " => IsInfix

/-- not `isInfix` -/
recommended_spelling "infix" for "<:+:" in [IsInfix, «term_<:+:_»]

/-! ### splitAt -/

/--
Splits a list at an index, resulting in the first `n` elements of `l` paired with the remaining
elements.

If `n` is greater than the length of `l`, then the resulting pair consists of `l` and the empty
list. `List.splitAt` is equivalent to a combination of `List.take` and `List.drop`, but it is more
efficient.

Examples:
* `["red", "green", "blue"].splitAt 2 = (["red", "green"], ["blue"])`
* `["red", "green", "blue"].splitAt 3 = (["red", "green", "blue], [])`
* `["red", "green", "blue"].splitAt 4 = (["red", "green", "blue], [])`
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
Rotates the elements of `xs` to the left, moving `i % xs.length` elements from the start of the list
to the end.

`O(|xs|)`.

Examples:
* `[1, 2, 3, 4, 5].rotateLeft 3 = [4, 5, 1, 2, 3]`
* `[1, 2, 3, 4, 5].rotateLeft 5 = [1, 2, 3, 4, 5]`
* `[1, 2, 3, 4, 5].rotateLeft 1 = [2, 3, 4, 5, 1]`
-/
def rotateLeft (xs : List α) (i : Nat := 1) : List α :=
  let len := xs.length
  if len ≤ 1 then
    xs
  else
    let i := i % len
    let ys := xs.take i
    let zs := xs.drop i
    zs ++ ys

@[simp] theorem rotateLeft_nil : ([] : List α).rotateLeft n = [] := rfl

/-! ### rotateRight -/
/--
Rotates the elements of `xs` to the right, moving `i % xs.length` elements from the end of the list
to the start.

After rotation, the element at `xs[n]` is at index `(i + n) % l.length`. `O(|xs|)`.

Examples:
* `[1, 2, 3, 4, 5].rotateRight 3 = [3, 4, 5, 1, 2]`
* `[1, 2, 3, 4, 5].rotateRight 5 = [1, 2, 3, 4, 5]`
* `[1, 2, 3, 4, 5].rotateRight 1 = [5, 1, 2, 3, 4]`
-/
def rotateRight (xs : List α) (i : Nat := 1) : List α :=
  let len := xs.length
  if len ≤ 1 then
    xs
  else
    let i := len - i % len
    let ys := xs.take i
    let zs := xs.drop i
    zs ++ ys

@[simp] theorem rotateRight_nil : ([] : List α).rotateRight n = [] := rfl

/-! ## Pairwise, Nodup -/

section Pairwise

variable (R : α → α → Prop)

/--
Each element of a list is related to all later elements of the list by `R`.

`Pairwise R l` means that all the elements of `l` with earlier indexes are `R`-related to all the
elements with later indexes.

For example, `Pairwise (· ≠ ·) l` asserts that `l` has no duplicates, and `Pairwise (· < ·) l`
asserts that `l` is (strictly) sorted.

Examples:
 * `Pairwise (· < ·) [1, 2, 3] ↔ (1 < 2 ∧ 1 < 3) ∧ 2 < 3`
 * `Pairwise (· = ·) [1, 2, 3] = False`
 * `Pairwise (· ≠ ·) [1, 2, 3] = True`
-/
inductive Pairwise : List α → Prop
  /-- All elements of the empty list are vacuously pairwise related. -/
  | nil : Pairwise []
  /--
  A nonempty list is pairwise related with `R` if the head is related to every element of the tail
  and the tail is itself pairwise related.

  That is, `a :: l` is `Pairwise R` if:
   * `R` relates `a` to every element of `l`
   * `l` is `Pairwise R`.
  -/
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

/--
The list has no duplicates: it contains every element at most once.

It is defined as `Pairwise (· ≠ ·)`: each element is unequal to all other elements.
-/
def Nodup : List α → Prop := Pairwise (· ≠ ·)

instance nodupDecidable [DecidableEq α] : ∀ l : List α, Decidable (Nodup l) :=
  instDecidablePairwise

/-! ## Manipulating elements -/

/-! ### replace -/

/--
Replaces the first element of the list `l` that is equal to `a` with `b`. If no element is equal to
`a`, then the list is returned unchanged.

`O(|l|)`.

Examples:
* `[1, 4, 2, 3, 3, 7].replace 3 6 = [1, 4, 2, 6, 3, 7]`
* `[1, 4, 2, 3, 3, 7].replace 5 6 = [1, 4, 2, 3, 3, 7]`
-/
def replace [BEq α] : (l : List α) → (a : α) → (b : α) → List α
  | [],    _, _ => []
  | a::as, b, c => match b == a with
    | true  => c::as
    | false => a :: replace as b c

@[simp, grind =] theorem replace_nil [BEq α] : ([] : List α).replace a b = [] := rfl
@[grind =] theorem replace_cons [BEq α] {a : α} :
    (a::as).replace b c = match b == a with | true => c::as | false => a :: replace as b c :=
  rfl

/-! ### modify -/

/--
Replaces the `n`th tail of `l` with the result of applying `f` to it. Returns the input without
using `f` if the index is larger than the length of the List.

Examples:
```lean example
["circle", "square", "triangle"].modifyTailIdx 1 List.reverse
```
```output
["circle", "triangle", "square"]
```
```lean example
["circle", "square", "triangle"].modifyTailIdx 1 (fun xs => xs ++ xs)
```
```output
["circle", "square", "triangle", "square", "triangle"]
```
```lean example
["circle", "square", "triangle"].modifyTailIdx 2 (fun xs => xs ++ xs)
```
```output
["circle", "square", "triangle", "triangle"]
```
```lean example
["circle", "square", "triangle"].modifyTailIdx 5 (fun xs => xs ++ xs)
```
```output
["circle", "square", "triangle"]
```
-/
def modifyTailIdx (l : List α) (i : Nat) (f : List α → List α) : List α :=
  go i l
where
  go : Nat → List α → List α
  | 0, l => f l
  | _+1, [] => []
  | i+1, a :: l => a :: go i l

@[simp] theorem modifyTailIdx_zero {l : List α} : l.modifyTailIdx 0 f = f l := rfl
@[simp] theorem modifyTailIdx_succ_nil {i : Nat} : ([] : List α).modifyTailIdx (i + 1) f = [] := rfl
@[simp] theorem modifyTailIdx_succ_cons {i : Nat} {a : α} {l : List α} :
    (a :: l).modifyTailIdx (i + 1) f = a :: l.modifyTailIdx i f := rfl

/--
Replace the head of the list with the result of applying `f` to it. Returns the empty list if the
list is empty.

Examples:
 * `[1, 2, 3].modifyHead (· * 10) = [10, 2, 3]`
 * `[].modifyHead (· * 10) = []`
-/
@[inline] def modifyHead (f : α → α) : List α → List α
  | [] => []
  | a :: l => f a :: l

@[simp] theorem modifyHead_nil {f : α → α} : [].modifyHead f = [] := by rw [modifyHead]
@[simp] theorem modifyHead_cons {a : α} {l : List α} {f : α → α} :
    (a :: l).modifyHead f = f a :: l := by rw [modifyHead]

/--
Replaces the element at the given index, if it exists, with the result of applying `f` to it. If the
index is invalid, the list is returned unmodified.

Examples:
 * `[1, 2, 3].modify 0 (· * 10) = [10, 2, 3]`
 * `[1, 2, 3].modify 2 (· * 10) = [1, 2, 30]`
 * `[1, 2, 3].modify 3 (· * 10) = [1, 2, 3]`
-/
def modify (l : List α) (i : Nat) (f : α → α) : List α :=
  l.modifyTailIdx i (modifyHead f)

/-! ### insert -/

/--
Inserts an element into a list without duplication.

If the element is present in the list, the list is returned unmodified. Otherwise, the new element
is inserted at the head of the list.

Examples:
 * `[1, 2, 3].insert 0 = [0, 1, 2, 3]`
 * `[1, 2, 3].insert 4 = [4, 1, 2, 3]`
 * `[1, 2, 3].insert 2 = [1, 2, 3]`
-/
@[inline] protected def insert [BEq α] (a : α) (l : List α) : List α :=
  if l.contains a then l else a :: l

/--
Inserts an element into a list at the specified index. If the index is greater than the length of
the list, then the list is returned unmodified.

In other words, the new element is inserted into the list `l` after the first `i` elements of `l`.

Examples:
 * `["tues", "thur", "sat"].insertIdx 1 "wed" = ["tues", "wed", "thur", "sat"]`
 * `["tues", "thur", "sat"].insertIdx 2 "wed" = ["tues", "thur", "wed", "sat"]`
 * `["tues", "thur", "sat"].insertIdx 3 "wed" = ["tues", "thur", "sat", "wed"]`
 * `["tues", "thur", "sat"].insertIdx 4 "wed" = ["tues", "thur", "sat"]`
-/
def insertIdx (xs : List α) (i : Nat) (a : α) : List α :=
  xs.modifyTailIdx i (cons a)

/-! ### erase -/

/--
Removes the first occurrence of `a` from `l`. If `a` does not occur in `l`, the list is returned
unmodified.

`O(|l|)`.

Examples:
* `[1, 5, 3, 2, 5].erase 5 = [1, 3, 2, 5]`
* `[1, 5, 3, 2, 5].erase 6 = [1, 5, 3, 2, 5]`
-/
protected def erase {α} [BEq α] : List α → α → List α
  | [],    _ => []
  | a::as, b => match a == b with
    | true  => as
    | false => a :: List.erase as b

@[simp, grind =] theorem erase_nil [BEq α] (a : α) : [].erase a = [] := rfl
@[grind =] theorem erase_cons [BEq α] {a b : α} {l : List α} :
    (b :: l).erase a = if b == a then l else b :: l.erase a := by
  simp only [List.erase]; split <;> simp_all

/--
Removes the first element of a list for which `p` returns `true`. If no element satisfies `p`, then
the list is returned unchanged.

Examples:
  * `[2, 1, 2, 1, 3, 4].eraseP (· < 2) = [2, 2, 1, 3, 4]`
  * `[2, 1, 2, 1, 3, 4].eraseP (· > 2) = [2, 1, 2, 1, 4]`
  * `[2, 1, 2, 1, 3, 4].eraseP (· > 8) = [2, 1, 2, 1, 3, 4]`
-/
def eraseP (p : α → Bool) : List α → List α
  | [] => []
  | a :: l => bif p a then l else a :: eraseP p l

/-! ### eraseIdx -/

/--
Removes the element at the specified index. If the index is out of bounds, the list is returned
unmodified.

`O(i)`.

Examples:
* `[0, 1, 2, 3, 4].eraseIdx 0 = [1, 2, 3, 4]`
* `[0, 1, 2, 3, 4].eraseIdx 1 = [0, 2, 3, 4]`
* `[0, 1, 2, 3, 4].eraseIdx 5 = [0, 1, 2, 3, 4]`
-/
def eraseIdx : (l : List α) → (i : Nat) → List α
  | [],    _   => []
  | _::as, 0   => as
  | a::as, n+1 => a :: eraseIdx as n

@[simp] theorem eraseIdx_nil : ([] : List α).eraseIdx i = [] := rfl
@[simp] theorem eraseIdx_cons_zero : (a::as).eraseIdx 0 = as := rfl
@[simp] theorem eraseIdx_cons_succ : (a::as).eraseIdx (i+1) = a :: as.eraseIdx i := rfl

/-! Finding elements -/

/-! ### find? -/

/--
Returns the first element of the list for which the predicate `p` returns `true`, or `none` if no
such element is found.

`O(|l|)`.

Examples:
* `[7, 6, 5, 8, 1, 2, 6].find? (· < 5) = some 1`
* `[7, 6, 5, 8, 1, 2, 6].find? (· < 1) = none`
-/
def find? (p : α → Bool) : List α → Option α
  | []    => none
  | a::as => match p a with
    | true  => some a
    | false => find? p as

@[simp, grind =] theorem find?_nil : ([] : List α).find? p = none := rfl
@[grind =]theorem find?_cons : (a::as).find? p = match p a with | true => some a | false => as.find? p :=
  rfl

/-! ### findSome? -/

/--
Returns the first non-`none` result of applying `f` to each element of the list in order. Returns
`none` if `f` returns `none` for all elements of the list.

`O(|l|)`.

Examples:
 * `[7, 6, 5, 8, 1, 2, 6].findSome? (fun x => if x < 5 then some (10 * x) else none) = some 10`
 * `[7, 6, 5, 8, 1, 2, 6].findSome? (fun x => if x < 1 then some (10 * x) else none) = none`
-/
def findSome? (f : α → Option β) : List α → Option β
  | []    => none
  | a::as => match f a with
    | some b => some b
    | none   => findSome? f as

@[simp, grind =] theorem findSome?_nil : ([] : List α).findSome? f = none := rfl
@[grind =] theorem findSome?_cons {f : α → Option β} :
    (a::as).findSome? f = match f a with | some b => some b | none => as.findSome? f :=
  rfl

/-! ### findRev? -/

/--
Returns the last element of the list for which the predicate `p` returns `true`, or `none` if no
such element is found.

`O(|l|)`.

Examples:
* `[7, 6, 5, 8, 1, 2, 6].findRev? (· < 5) = some 2`
* `[7, 6, 5, 8, 1, 2, 6].findRev? (· < 1) = none`
-/
def findRev? (p : α → Bool) : List α → Option α
  | []    => none
  | a::as => match findRev? p as with
    | some b => some b
    | none   => if p a then some a else none

/-! ### findSomeRev? -/

/--
Returns the last non-`none` result of applying `f` to each element of the list in order. Returns
`none` if `f` returns `none` for all elements of the list.

`O(|l|)`.

Examples:
 * `[7, 6, 5, 8, 1, 2, 6].findSomeRev? (fun x => if x < 5 then some (10 * x) else none) = some 20`
 * `[7, 6, 5, 8, 1, 2, 6].findSomeRev? (fun x => if x < 1 then some (10 * x) else none) = none`
-/
def findSomeRev? (f : α → Option β) : List α → Option β
  | []    => none
  | a::as => match findSomeRev? f as with
    | some b => some b
    | none   => f a

/-! ### findIdx -/

/--
Returns the index of the first element for which `p` returns `true`, or the length of the list if
there is no such element.

Examples:
* `[7, 6, 5, 8, 1, 2, 6].findIdx (· < 5) = 4`
* `[7, 6, 5, 8, 1, 2, 6].findIdx (· < 1) = 7`
-/
@[inline] def findIdx (p : α → Bool) (l : List α) : Nat := go l 0 where
  /-- Auxiliary for `findIdx`: `findIdx.go p l n = findIdx p l + n` -/
  @[specialize] go : List α → Nat → Nat
  | [], n => n
  | a :: l, n => bif p a then n else go l (n + 1)

@[simp] theorem findIdx_nil {p : α → Bool} : [].findIdx p = 0 := rfl

/-! ### idxOf -/

/--
Returns the index of the first element equal to `a`, or the length of the list if no element is
equal to `a`.

Examples:
 * `["carrot", "potato", "broccoli"].idxOf "carrot" = 0`
 * `["carrot", "potato", "broccoli"].idxOf "broccoli" = 2`
 * `["carrot", "potato", "broccoli"].idxOf "tomato" = 3`
 * `["carrot", "potato", "broccoli"].idxOf "anything else" = 3`
-/
def idxOf [BEq α] (a : α) : List α → Nat := findIdx (· == a)

@[simp] theorem idxOf_nil [BEq α] : ([] : List α).idxOf x = 0 := rfl

/-! ### findIdx? -/

/--
Returns the index of the first element for which `p` returns `true`, or `none` if there is no such
element.

Examples:
* `[7, 6, 5, 8, 1, 2, 6].findIdx (· < 5) = some 4`
* `[7, 6, 5, 8, 1, 2, 6].findIdx (· < 1) = none`
-/
def findIdx? (p : α → Bool) (l : List α) : Option Nat :=
  go l 0
where
  go : List α → Nat → Option Nat
  | [], _ => none
  | a :: l, i => if p a then some i else go l (i + 1)

/-! ### idxOf? -/

/--
Returns the index of the first element equal to `a`, or `none` if no element is equal to `a`.

Examples:
 * `["carrot", "potato", "broccoli"].idxOf? "carrot" = some 0`
 * `["carrot", "potato", "broccoli"].idxOf? "broccoli" = some 2`
 * `["carrot", "potato", "broccoli"].idxOf? "tomato" = none`
 * `["carrot", "potato", "broccoli"].idxOf? "anything else" = none`
-/
@[inline] def idxOf? [BEq α] (a : α) : List α → Option Nat := findIdx? (· == a)

/-! ### findFinIdx? -/

/--
Returns the index of the first element for which `p` returns `true`, or `none` if there is no such
element. The index is returned as a `Fin`, which guarantees that it is in bounds.

Examples:
* `[7, 6, 5, 8, 1, 2, 6].findFinIdx? (· < 5) = some (4 : Fin 7)`
* `[7, 6, 5, 8, 1, 2, 6].findFinIdx? (· < 1) = none`
-/
@[inline] def findFinIdx? (p : α → Bool) (l : List α) : Option (Fin l.length) :=
  go l 0 (by simp)
where
  go : (l' : List α) → (i : Nat) → (h : l'.length + i = l.length) → Option (Fin l.length)
  | [], _, _ => none
  | a :: l, i, h =>
    if p a then
      some ⟨i, by
        simp only [Nat.add_comm _ i] at h
        exact Nat.lt_of_add_right_lt (Nat.lt_of_succ_le (Nat.le_of_eq h))⟩
    else
      go l (i + 1) (by simp at h; simpa [← Nat.add_assoc, Nat.add_right_comm] using h)

/-! ### finIdxOf? -/

/--
Returns the index of the first element equal to `a`, or the length of the list if no element is
equal to `a`. The index is returned as a `Fin`, which guarantees that it is in bounds.

Examples:
 * `["carrot", "potato", "broccoli"].finIdxOf? "carrot" = some 0`
 * `["carrot", "potato", "broccoli"].finIdxOf? "broccoli" = some 2`
 * `["carrot", "potato", "broccoli"].finIdxOf? "tomato" = none`
 * `["carrot", "potato", "broccoli"].finIdxOf? "anything else" = none`
-/
@[inline] def finIdxOf? [BEq α] (a : α) : (l : List α) → Option (Fin l.length) :=
  findFinIdx? (· == a)

/-! ### countP -/

/--
Counts the number of elements in the list `l` that satisfy the Boolean predicate `p`.

Examples:
 * `[1, 2, 3, 4, 5].countP (· % 2 == 0) = 2`
 * `[1, 2, 3, 4, 5].countP (· < 5) = 4`
 * `[1, 2, 3, 4, 5].countP (· > 5) = 0`
-/
@[inline] def countP (p : α → Bool) (l : List α) : Nat := go l 0 where
  /-- Auxiliary for `countP`: `countP.go p l acc = countP p l + acc`. -/
  @[specialize] go : List α → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => bif p x then go xs (acc + 1) else go xs acc

/-! ### count -/

/--
Counts the number of times an element occurs in a list.

Examples:
 * `[1, 1, 2, 3, 5].count 1 = 2`
 * `[1, 1, 2, 3, 5].count 5 = 1`
 * `[1, 1, 2, 3, 5].count 4 = 0`
-/
@[inline] def count [BEq α] (a : α) : List α → Nat := countP (· == a)

/-! ### lookup -/

/--
Treats the list as an association list that maps keys to values, returning the first value whose key
is equal to the specified key.

`O(|l|)`.

Examples:
* `[(1, "one"), (3, "three"), (3, "other")].lookup 3 = some "three"`
* `[(1, "one"), (3, "three"), (3, "other")].lookup 2 = none`
-/
def lookup [BEq α] : α → List (α × β) → Option β
  | _, []           => none
  | a, (k, b) :: as => match a == k with
    | true  => some b
    | false => lookup a as

@[simp, grind =] theorem lookup_nil [BEq α] : ([] : List (α × β)).lookup a = none := rfl
@[grind =] theorem lookup_cons [BEq α] {k : α} :
    ((k, b)::as).lookup a = match a == k with | true => some b | false => as.lookup a :=
  rfl

/-! ## Permutations -/

/-! ### Perm -/

/--
Two lists are permutations of each other if they contain the same elements, each occurring the same
number of times but not necessarily in the same order.

One list can be proven to be a permutation of another by showing how to transform one into the other
by repeatedly swapping adjacent elements.

`List.isPerm` is a Boolean equivalent of this relation.
-/
inductive Perm : List α → List α → Prop
  /-- The empty list is a permutation of the empty list: `[] ~ []`. -/
  | nil : Perm [] []
  /--
  If one list is a permutation of the other, adding the same element as the head of each yields
  lists that are permutations of each other: `l₁ ~ l₂ → x::l₁ ~ x::l₂`.
  -/
  | cons (x : α) {l₁ l₂ : List α} : Perm l₁ l₂ → Perm (x :: l₁) (x :: l₂)
  /--
  If two lists are identical except for having their first two elements swapped, then they are
  permutations of each other: `x::y::l ~ y::x::l`.
  -/
  | swap (x y : α) (l : List α) : Perm (y :: x :: l) (x :: y :: l)
  /--
  Permutation is transitive: `l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃`.
  -/
  | trans {l₁ l₂ l₃ : List α} : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

@[inherit_doc] scoped infixl:50 " ~ " => Perm

/-! ### isPerm -/

/--
Returns `true` if `l₁` and `l₂` are permutations of each other. `O(|l₁| * |l₂|)`.

The relation `List.Perm` is a logical characterization of permutations. When the `BEq α` instance
corresponds to `DecidableEq α`, `isPerm l₁ l₂ ↔ l₁ ~ l₂` (use the theorem `isPerm_iff`).
-/
def isPerm [BEq α] : List α → List α → Bool
  | [], l₂ => l₂.isEmpty
  | a :: l₁, l₂ => l₂.contains a && l₁.isPerm (l₂.erase a)

/-! ## Logical operations -/

/-! ### any -/

/--
Returns `true` if `p` returns `true` for any element of `l`.

`O(|l|)`. Short-circuits upon encountering the first `true`.

Examples:
* `[2, 4, 6].any (· % 2 = 0) = true`
* `[2, 4, 6].any (· % 2 = 1) = false`
* `[2, 4, 5, 6].any (· % 2 = 0) = true`
* `[2, 4, 5, 6].any (· % 2 = 1) = true`
-/
@[suggest_for List.some]
def any : (l : List α) → (p : α → Bool) → Bool
  | [], _ => false
  | h :: t, p => p h || any t p

@[simp, grind =] theorem any_nil : [].any f = false := rfl
@[simp, grind =] theorem any_cons : (a::l).any f = (f a || l.any f) := rfl

/-! ### all -/

/--
Returns `true` if `p` returns `true` for every element of `l`.

`O(|l|)`. Short-circuits upon encountering the first `false`.

Examples:
* `[a, b, c].all p = (p a && (p b && p c))`
* `[2, 4, 6].all (· % 2 = 0) = true`
* `[2, 4, 5, 6].all (· % 2 = 0) = false`
-/
@[suggest_for List.every]
def all : List α → (α → Bool) → Bool
  | [], _ => true
  | h :: t, p => p h && all t p

@[simp, grind =] theorem all_nil : [].all f = true := rfl
@[simp, grind =] theorem all_cons : (a::l).all f = (f a && l.all f) := rfl

/-! ### or -/

/--
Returns `true` if `true` is an element of the list `bs`.

`O(|bs|)`. Short-circuits at the first `true` value.

* `[true, true, true].or = true`
* `[true, false, true].or = true`
* `[false, false, false].or = false`
* `[false, false, true].or = true`
* `[].or = false`
-/
def or (bs : List Bool) : Bool := bs.any id

@[simp] theorem or_nil : [].or = false := rfl
@[simp] theorem or_cons : (a::l).or = (a || l.or) := rfl

/-! ### and -/

/--
Returns `true` if every element of `bs` is the value `true`.

`O(|bs|)`. Short-circuits at the first `false` value.

* `[true, true, true].and = true`
* `[true, false, true].and = false`
* `[true, false, false].and = false`
* `[].and = true`
-/
def and (bs : List Bool) : Bool := bs.all id

@[simp] theorem and_nil : [].and = true := rfl
@[simp] theorem and_cons : (a::l).and = (a && l.and) := rfl

/-! ## Zippers -/

/-! ### zipWith -/

/--
Applies a function to the corresponding elements of two lists, stopping at the end of the shorter
list.

`O(min |xs| |ys|)`.

Examples:
* `[1, 2].zipWith (· + ·) [5, 6] = [6, 8]`
* `[1, 2, 3].zipWith (· + ·) [5, 6, 10] = [6, 8, 13]`
* `[].zipWith (· + ·) [5, 6] = []`
* `[x₁, x₂, x₃].zipWith f [y₁, y₂, y₃, y₄] = [f x₁ y₁, f x₂ y₂, f x₃ y₃]`
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
Combines two lists into a list of pairs in which the first and second components are the
corresponding elements of each list. The resulting list is the length of the shorter of the input
lists.

`O(min |xs| |ys|)`.

Examples:
* `["Mon", "Tue", "Wed"].zip [1, 2, 3] = [("Mon", 1), ("Tue", 2), ("Wed", 3)]`
* `["Mon", "Tue", "Wed"].zip [1, 2] = [("Mon", 1), ("Tue", 2)]`
* `[x₁, x₂, x₃].zip [y₁, y₂, y₃, y₄] = [(x₁, y₁), (x₂, y₂), (x₃, y₃)]`
-/
def zip : List α → List β → List (Prod α β) :=
  zipWith Prod.mk

@[simp] theorem zip_nil_left : zip ([] : List α) (l : List β)  = [] := rfl
@[simp] theorem zip_nil_right : zip (l : List α) ([] : List β)  = [] := by simp [zip]
@[simp] theorem zip_cons_cons : zip (a :: as) (b :: bs) = (a, b) :: zip as bs := rfl

/-! ### zipWithAll -/

/--
Applies a function to the corresponding elements of both lists, stopping when there are no more
elements in either list. If one list is shorter than the other, the function is passed `none` for
the missing elements.

Examples:
* `[1, 6].zipWithAll min [5, 2] = [some 1, some 2]`
* `[1, 2, 3].zipWithAll Prod.mk [5, 6] = [(some 1, some 5), (some 2, some 6), (some 3, none)]`
* `[x₁, x₂].zipWithAll f [y] = [f (some x₁) (some y), f (some x₂) none]`
-/
def zipWithAll (f : Option α → Option β → γ) : List α → List β → List γ
  | [], bs => bs.map fun b => f none (some b)
  | a :: as, [] => (a :: as).map fun a => f (some a) none
  | a :: as, b :: bs => f (some a) (some b) :: zipWithAll f as bs

@[simp] theorem zipWithAll_nil :
    zipWithAll f as [] = as.map fun a => f (some a) none := by
  cases as <;> rfl
@[simp] theorem nil_zipWithAll :
    zipWithAll f [] bs = bs.map fun b => f none (some b) := rfl
@[simp] theorem zipWithAll_cons_cons :
    zipWithAll f (a :: as) (b :: bs) = f (some a) (some b) :: zipWithAll f as bs := rfl

/-! ### unzip -/

/--
Separates a list of pairs into two lists that contain the respective first and second components.

`O(|l|)`.

Examples:
* `[("Monday", 1), ("Tuesday", 2)].unzip = (["Monday", "Tuesday"], [1, 2])`
* `[(x₁, y₁), (x₂, y₂), (x₃, y₃)].unzip = ([x₁, x₂, x₃], [y₁, y₂, y₃])`
* `([] : List (Nat × String)).unzip = (([], []) : List Nat × List String)`
-/
def unzip : (l : List (α × β)) → List α × List β
  | []          => ([], [])
  | (a, b) :: t => match unzip t with | (as, bs) => (a::as, b::bs)

@[simp] theorem unzip_nil : ([] : List (α × β)).unzip = ([], []) := rfl
@[simp] theorem unzip_cons {h : α × β} :
    (h :: t).unzip = match unzip t with | (as, bs) => (h.1::as, h.2::bs) := rfl

/-! ## Ranges and enumeration -/

/--
Computes the sum of the elements of a list.

Examples:
 * `[a, b, c].sum = a + (b + (c + 0))`
 * `[1, 2, 5].sum = 8`
-/
def sum {α} [Add α] [Zero α] : List α → α :=
  foldr (· + ·) 0

@[simp, grind =] theorem sum_nil [Add α] [Zero α] : ([] : List α).sum = 0 := rfl
@[simp, grind =] theorem sum_cons [Add α] [Zero α] {a : α} {l : List α} : (a::l).sum = a + l.sum := rfl
theorem sum_eq_foldr [Add α] [Zero α] {l : List α} : l.sum = l.foldr (· + ·) 0 := rfl

/-! ### range -/

/--
Returns a list of the numbers from `0` to `n` exclusive, in increasing order.

`O(n)`.

Examples:
* `range 5 = [0, 1, 2, 3, 4]`
* `range 0 = []`
* `range 2 = [0, 1]`
-/
def range (n : Nat) : List Nat :=
  loop n []
where
  loop : Nat → List Nat → List Nat
  | 0,   acc => acc
  | n+1, acc => loop n (n::acc)

@[simp, grind =] theorem range_zero : range 0 = [] := rfl

/-! ### range' -/

/--
Returns a list of the numbers with the given length `len`, starting at `start` and increasing by
`step` at each element.

In other words, `List.range' start len step` is `[start, start+step, ..., start+(len-1)*step]`.

Examples:
 * `List.range' 0 3 (step := 1) = [0, 1, 2]`
 * `List.range' 0 3 (step := 2) = [0, 2, 4]`
 * `List.range' 0 4 (step := 2) = [0, 2, 4, 6]`
 * `List.range' 3 4 (step := 2) = [3, 5, 7, 9]`
-/
def range' : (start len : Nat) → (step : Nat := 1) → List Nat
  | _, 0, _ => []
  | s, n+1, step => s :: range' (s+step) n step

@[simp, grind =] theorem range'_zero : range' s 0 step = [] := rfl
@[simp, grind =] theorem range'_one {s step : Nat} : range' s 1 step = [s] := rfl
-- The following theorem is intentionally not a simp lemma.
theorem range'_succ : range' s (n + 1) step = s :: range' (s + step) n step := rfl

/-! ### zipIdx -/

/--
Pairs each element of a list with its index, optionally starting from an index other than `0`.

`O(|l|)`.

Examples:
* `[a, b, c].zipIdx = [(a, 0), (b, 1), (c, 2)]`
* `[a, b, c].zipIdx 5 = [(a, 5), (b, 6), (c, 7)]`
-/
def zipIdx : (l : List α) → (n : Nat := 0) → List (α × Nat)
  | [], _ => nil
  | x :: xs, n => (x, n) :: zipIdx xs (n + 1)

@[simp] theorem zipIdx_nil : ([] : List α).zipIdx i = [] := rfl
@[simp] theorem zipIdx_cons : (a::as).zipIdx i = (a, i) :: as.zipIdx (i+1) := rfl

/-! ## Minima and maxima -/

/-! ### min? -/

/--
Returns the smallest element of the list if it is not empty, or `none` if it is empty.

Examples:
* `[].min? = none`
* `[4].min? = some 4`
* `[1, 4, 2, 10, 6].min? = some 1`
-/
def min? [Min α] : List α → Option α
  | []    => none
  | a::as => some <| as.foldl min a

/-! ### min -/

/--
Returns the smallest element of a non-empty list.

Examples:
* `[4].min (by decide) = 4`
* `[1, 4, 2, 10, 6].min (by decide) = 1`
-/
protected def min [Min α] : (l : List α) → (h : l ≠ []) → α
  | a::as, _ => as.foldl min a

/-! ### max? -/

/--
Returns the largest element of the list if it is not empty, or `none` if it is empty.

Examples:
* `[].max? = none`
* `[4].max? = some 4`
* `[1, 4, 2, 10, 6].max? = some 10`
-/
def max? [Max α] : List α → Option α
  | []    => none
  | a::as => some <| as.foldl max a

/-! ### max -/

/--
Returns the largest element of a non-empty list.

Examples:
* `[4].max (by decide) = 4`
* `[1, 4, 2, 10, 6].max (by decide) = 10`
-/
protected def max [Max α] : (l : List α) → (h : l ≠ []) → α
  | a::as, _ => as.foldl max a

/-! ## Other list operations

The functions are currently mostly used in meta code,
and do not have sufficient API developed for verification work.
-/

/-! ### intersperse -/

/--
Alternates the elements of `l` with `sep`.

`O(|l|)`.

`List.intercalate` is a similar function that alternates a separator list with elements of a list of
lists.

Examples:
* `List.intersperse "then" [] = []`
* `List.intersperse "then" ["walk"] = ["walk"]`
* `List.intersperse "then" ["walk", "run"] = ["walk", "then", "run"]`
* `List.intersperse "then" ["walk", "run", "rest"] = ["walk", "then", "run", "then", "rest"]`
-/
def intersperse (sep : α) : (l : List α) → List α
  | []    => []
  | [x]   => [x]
  | x::xs => x :: sep :: intersperse sep xs

@[simp] theorem intersperse_nil {sep : α} : ([] : List α).intersperse sep = [] := rfl
@[simp] theorem intersperse_singleton {x : α} {sep : α} : [x].intersperse sep = [x] := rfl
@[deprecated intersperse_singleton (since := "2026-02-26")]
theorem intersperse_single {x : α} {sep : α} : [x].intersperse sep = [x] := rfl
@[simp] theorem intersperse_cons_cons {x : α} {y : α} {zs : List α} {sep : α} :
    (x::y::zs).intersperse sep = x::sep::((y::zs).intersperse sep) := rfl

@[deprecated intersperse_cons_cons (since := "2026-02-26")]
theorem intersperse_cons₂ {x : α} {y : α} {zs : List α} {sep : α} :
    (x::y::zs).intersperse sep = x::sep::((y::zs).intersperse sep) := intersperse_cons_cons

/-! ### intercalate -/

set_option linter.listVariables false in
/--
Alternates the lists in `xs` with the separator `sep`, appending them. The resulting list is
flattened.

`O(|xs|)`.

`List.intersperse` is a similar function that alternates a separator element with the elements of a
list.

Examples:
* `List.intercalate sep [] = []`
* `List.intercalate sep [a] = a`
* `List.intercalate sep [a, b] = a ++ sep ++ b`
* `List.intercalate sep [a, b, c] = a ++ sep ++ b ++ sep ++ c`
-/
noncomputable def intercalate (sep : List α) (xs : List (List α)) : List α :=
  (intersperse sep xs).flatten

/-! ### eraseDupsBy -/

/--
Erases duplicated elements in the list, using a given comparison function,
keeping the first occurrence of duplicated elements.

`O(|l|^2)`.

Examples:
 * `[1, 3, 4, 2, 1, 5].eraseDupsBy (· % 3 == · % 3) = [1, 3, 2]`
-/
def eraseDupsBy {α} (r : α → α → Bool) (as : List α) : List α :=
  loop as []
where
  loop : List α → List α → List α
  | [],    bs => bs.reverse
  | a::as, bs => match bs.any (r a) with
    | true  => loop as bs
    | false => loop as (a::bs)

/-! ### eraseDups -/

/--
Erases duplicated elements in the list, keeping the first occurrence of duplicated elements.

`O(|l|^2)`.

Examples:
 * `[1, 3, 2, 2, 3, 5].eraseDups = [1, 3, 2, 5]`
 * `["red", "green", "green", "blue"].eraseDups = ["red", "green", "blue"]`
-/
def eraseDups {α} [BEq α] (as : List α) : List α := eraseDupsBy (· == ·) as

/-! ### eraseRepsBy -/

/--
Erases repeated elements, using a given comparison function,
keeping the first element of each run.

`O(|l|)`.

Example:
* `[1, 3, 2, 2, 2, 3, 3, 7].eraseRepsBy (· % 4 == · % 5) = [1, 3, 2, 3]`
-/
def eraseRepsBy {α} (r : α → α → Bool) : List α → List α
  | []    => []
  | a::as => loop a as []
where
  loop : α → List α → List α → List α
  | a, [], acc => (a::acc).reverse
  | a, a'::as, acc => match r a a' with
    | true  => loop a as acc
    | false => loop a' as (a::acc)

/-! ### eraseReps -/

/--
Erases repeated elements, keeping the first element of each run.

`O(|l|)`.

Example:
* `[1, 3, 2, 2, 2, 3, 3, 5].eraseReps = [1, 3, 2, 3, 5]`
-/
def eraseReps {α} [BEq α] (as : List α) : List α := eraseRepsBy (· == ·) as

/-! ### span -/

/--
Splits a list into the longest initial segment for which `p` returns `true`, paired with the
remainder of the list.

`O(|l|)`.

Examples:
* `[6, 8, 9, 5, 2, 9].span (· > 5) = ([6, 8, 9], [5, 2, 9])`
* `[6, 8, 9, 5, 2, 9].span (· > 10) = ([], [6, 8, 9, 5, 2, 9])`
* `[6, 8, 9, 5, 2, 9].span (· > 0) = ([6, 8, 9, 5, 2, 9], [])`
-/
@[inline] def span (p : α → Bool) (as : List α) : List α × List α :=
  loop as []
where
  @[specialize] loop : List α → List α → List α × List α
  | [],    acc => (acc.reverse, [])
  | a::as, acc => match p a with
    | true  => loop as (a::acc)
    | false => (acc.reverse, a::as)

/-! ### splitBy -/

/--
Splits a list into the longest segments in which each pair of adjacent elements are related by `R`.

`O(|l|)`.

Examples:
* `[1, 1, 2, 2, 2, 3, 2].splitBy (· == ·) = [[1, 1], [2, 2, 2], [3], [2]]`
* `[1, 2, 5, 4, 5, 1, 4].splitBy (· < ·) = [[1, 2, 5], [4, 5], [1, 4]]`
* `[1, 2, 5, 4, 5, 1, 4].splitBy (fun _ _ => true) = [[1, 2, 5, 4, 5, 1, 4]]`
* `[1, 2, 5, 4, 5, 1, 4].splitBy (fun _ _ => false) = [[1], [2], [5], [4], [5], [1], [4]]`
-/
@[specialize] def splitBy (R : α → α → Bool) : List α → List (List α)
  | []    => []
  | a::as => loop as a [] []
where
  /--
  The arguments of `splitBy.loop l b g gs` represent the following:

  - `l : List α` are the elements which we still need to split.
  - `b : α` is the previous element for which a comparison was performed.
  - `r : List α` is the group currently being assembled, in **reverse order**.
  - `acc : List (List α)` is all of the groups that have been completed, in **reverse order**.
  -/
  @[specialize] loop : List α → α → List α → List (List α) → List (List α)
  | a::as, b, r, acc => match R b a with
    | true  => loop as a (b::r) acc
    | false => loop as a [] ((b::r).reverse::acc)
  | [], ag, r, acc => ((ag::r).reverse::acc).reverse

/-! ### removeAll -/

/--
Removes all elements of `xs` that are present in `ys`.

`O(|xs| * |ys|)`.

Examples:
 * `[1, 1, 5, 1, 2, 4, 5].removeAll [1, 2, 2] = [5, 4, 5]`
 * `[1, 2, 3, 2].removeAll [] = [1, 2, 3, 2]`
 * `[1, 2, 3, 2].removeAll [3] = [1, 2, 2]`
-/
def removeAll [BEq α] (xs ys : List α) : List α :=
  xs.filter (fun x => !ys.elem x)

@[simp] theorem nil_removeAll [BEq α] {ys : List α} : [].removeAll ys = [] := rfl

/-!
# Runtime re-implementations using `@[csimp]`

More of these re-implementations are provided in `Init/Data/List/Impl.lean`.
They can not be here, because the remaining ones required `Array` for their implementation.

This leaves a dangerous situation: if you import this file, but not `Init/Data/List/Impl.lean`,
then at runtime you will get non tail-recursive versions.
-/

/-! ### length -/

theorem length_add_eq_lengthTRAux {as : List α} {n : Nat} : as.length + n = as.lengthTRAux n := by
  induction as generalizing n with
  | nil  => simp [length, lengthTRAux]
  | cons a as ih =>
    simp [length, lengthTRAux, ← ih, Nat.succ_add]
    rfl

@[csimp] theorem length_eq_lengthTR : @List.length = @List.lengthTR := by
  apply funext; intro α; apply funext; intro as
  simp [lengthTR, ← length_add_eq_lengthTRAux]

/-! ### map -/

/--
Applies a function to each element of the list, returning the resulting list of values.

`O(|l|)`. This is the tail-recursive variant of `List.map`, used in runtime code.

Examples:
* `[a, b, c].mapTR f = [f a, f b, f c]`
* `[].mapTR Nat.succ = []`
* `["one", "two", "three"].mapTR (·.length) = [3, 3, 5]`
* `["one", "two", "three"].mapTR (·.reverse) = ["eno", "owt", "eerht"]`
-/
@[inline] def mapTR (f : α → β) (as : List α) : List β :=
  loop as []
where
  @[specialize] loop : List α → List β → List β
  | [],    bs => bs.reverse
  | a::as, bs => loop as (f a :: bs)

theorem mapTR_loop_eq {f : α → β} {as : List α} {bs : List β} :
    mapTR.loop f as bs = bs.reverse ++ map f as := by
  induction as generalizing bs with
  | nil => simp [mapTR.loop, map]
  | cons a as ih =>
    simp only [mapTR.loop, map]
    rw [ih (bs := f a :: bs), reverse_cons, append_assoc]
    rfl

@[csimp] theorem map_eq_mapTR : @map = @mapTR :=
  funext fun α => funext fun β => funext fun f => funext fun as => by
    simp [mapTR, mapTR_loop_eq]

/-! ### filter -/

/--
Returns the list of elements in `l` for which `p` returns `true`.

`O(|l|)`. This is a tail-recursive version of `List.filter`, used at runtime.

Examples:
* `[1, 2, 5, 2, 7, 7].filterTR (· > 2)  = [5, 7, 7]`
* `[1, 2, 5, 2, 7, 7].filterTR (fun _ => false) = []`
* `[1, 2, 5, 2, 7, 7].filterTR (fun _ => true) = * [1, 2, 5, 2, 7, 7]`
-/
@[inline] def filterTR (p : α → Bool) (as : List α) : List α :=
  loop as []
where
  @[specialize] loop : List α → List α → List α
  | [],    acc => acc.reverse
  | a::as, acc => match p a with
     | true  => loop as (a::acc)
     | false => loop as acc

theorem filterTR_loop_eq {p : α → Bool} {as : List α} {bs : List α} :
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

/--
Creates a list that contains `n` copies of `a`.

This is a tail-recursive version of `List.replicate`.

* `List.replicateTR 5 "five" = ["five", "five", "five", "five", "five"]`
* `List.replicateTR 0 "zero" = []`
* `List.replicateTR 2 ' ' = [' ', ' ']`
-/
def replicateTR {α : Type u} (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0, as => as
    | n+1, as => loop n (a::as)
  loop n []

theorem replicateTR_loop_replicate_eq {a : α} {m n : Nat} :
  replicateTR.loop a n (replicate m a) = replicate (n + m) a := by
  induction n generalizing m with simp [replicateTR.loop]
  | succ n ih => simp [Nat.succ_add]; exact ih (m := m+1)

theorem replicateTR_loop_eq : ∀ n, replicateTR.loop a n acc = replicate n a ++ acc
  | 0 => rfl
  | n+1 => by rw [← replicateTR_loop_replicate_eq, replicate, replicate,
    replicateTR.loop, replicateTR_loop_eq n, replicateTR_loop_eq n, append_assoc]; rfl

@[csimp] theorem replicate_eq_replicateTR : @List.replicate = @List.replicateTR := by
  apply funext; intro α; apply funext; intro n; apply funext; intro a
  exact (replicateTR_loop_replicate_eq (m := 0)).symm

/-! ## Additional functions -/

/-! ### leftpad -/

/--
Pads `l : List α` on the left with repeated occurrences of `a : α` until it is of length `n`. If `l`
already has at least `n` elements, it is returned unmodified.

This is a tail-recursive version of `List.leftpad`, used at runtime.

Examples:
 * `[1, 2, 3].leftPadTR 5 0 = [0, 0, 1, 2, 3]`
 * `["red", "green", "blue"].leftPadTR 4 "blank" = ["blank", "red", "green", "blue"]`
 * `["red", "green", "blue"].leftPadTR 3 "blank" = ["red", "green", "blue"]`
 * `["red", "green", "blue"].leftPadTR 1 "blank" = ["red", "green", "blue"]`
-/
@[inline] def leftpadTR (n : Nat) (a : α) (l : List α) : List α :=
  replicateTR.loop a (n - length l) l

@[csimp] theorem leftpad_eq_leftpadTR : @leftpad = @leftpadTR := by
  repeat (apply funext; intro)
  simp [leftpad, leftpadTR, replicateTR_loop_eq]


/-! ## Zippers -/

/-! ### unzip -/

/--
Separates a list of pairs into two lists that contain the respective first and second components.

`O(|l|)`. This is a tail-recursive version of `List.unzip` that's used at runtime.

Examples:
* `[("Monday", 1), ("Tuesday", 2)].unzipTR = (["Monday", "Tuesday"], [1, 2])`
* `[(x₁, y₁), (x₂, y₂), (x₃, y₃)].unzipTR = ([x₁, x₂, x₃], [y₁, y₂, y₃])`
* `([] : List (Nat × String)).unzipTR = (([], []) : List Nat × List String)`
-/
def unzipTR (l : List (α × β)) : List α × List β :=
  l.foldr (fun (a, b) (as, bs) => (a::as, b::bs)) ([], [])

@[csimp] theorem unzip_eq_unzipTR : @unzip = @unzipTR := by
  apply funext; intro α; apply funext; intro β; apply funext; intro l
  simp [unzipTR]; induction l <;> simp [*]

/-! ## Ranges and enumeration -/

/-! ### range' -/

/--
Returns a list of the numbers with the given length `len`, starting at `start` and increasing by
`step` at each element.

In other words, `List.range'TR start len step` is `[start, start+step, ..., start+(len-1)*step]`.

This is a tail-recursive version of `List.range'`.

Examples:
 * `List.range'TR 0 3 (step := 1) = [0, 1, 2]`
 * `List.range'TR 0 3 (step := 2) = [0, 2, 4]`
 * `List.range'TR 0 4 (step := 2) = [0, 2, 4, 6]`
 * `List.range'TR 3 4 (step := 2) = [3, 5, 7, 9]`
-/
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

/-! ## Other list operations -/

/-! ### intersperse -/

/--
Alternates the elements of `l` with `sep`.

`O(|l|)`.

This is a tail-recursive version of `List.intersperse`, used at runtime.

Examples:
* `List.intersperseTR "then" [] = []`
* `List.intersperseTR "then" ["walk"] = ["walk"]`
* `List.intersperseTR "then" ["walk", "run"] = ["walk", "then", "run"]`
* `List.intersperseTR "then" ["walk", "run", "rest"] = ["walk", "then", "run", "then", "rest"]`
-/
def intersperseTR (sep : α) : (l : List α) → List α
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
