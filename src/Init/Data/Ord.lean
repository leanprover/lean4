/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian, Sebastian Ullrich
-/

prelude
import Init.Data.String
import Init.Data.Array.Basic

/--
The result of a comparison according to a total order.

The relationship between the compared items may be:
 * `Ordering.lt`: less than
 * `Ordering.eq`: equal
 * `Ordering.gt`: greater than
-/
inductive Ordering where
  | /-- Less than. -/
    lt
  | /-- Equal. -/
    eq
  | /-- Greater than. -/
    gt
deriving Inhabited, DecidableEq

namespace Ordering

/--
Swaps less-than and greater-than ordering results.

Examples:
 * `Ordering.lt.swap = Ordering.gt`
 * `Ordering.eq.swap = Ordering.eq`
 * `Ordering.gt.swap = Ordering.lt`
-/
def swap : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

/--
If `a` and `b` are `Ordering`, then `a.then b` returns `a` unless it is `.eq`, in which case it
returns `b`. Additionally, it has “short-circuiting” behavior similar to boolean `&&`: if `a` is not
`.eq` then the expression for `b` is not evaluated.

This is a useful primitive for constructing lexicographic comparator functions. The `deriving Ord`
syntax on a structure uses the `Ord` instance to compare each field in order, combining the results
equivalently to `Ordering.then`.

Use `compareLex` to lexicographically combine two comparison functions.

Examples:
```lean example
structure Person where
  name : String
  age : Nat

-- Sort people first by name (in ascending order), and people with the same name by age (in
-- descending order)
instance : Ord Person where
  compare a b := (compare a.name b.name).then (compare b.age a.age)
```

```lean example
#eval Ord.compare (⟨"Gert", 33⟩ : Person) ⟨"Dana", 50⟩
```
```output
Ordering.gt
```

```lean example
#eval Ord.compare (⟨"Gert", 33⟩ : Person) ⟨"Gert", 50⟩
```
```output
Ordering.gt
```

```lean example
#eval Ord.compare (⟨"Gert", 33⟩ : Person) ⟨"Gert", 20⟩
```
```output
Ordering.lt
```
-/
@[macro_inline] def «then» (a b : Ordering) : Ordering :=
  match a with
  | .eq => b
  | a => a

/--
Checks whether the ordering is `eq`.
-/
def isEq : Ordering → Bool
  | eq => true
  | _ => false

/--
Checks whether the ordering is not `eq`.
-/
def isNe : Ordering → Bool
  | eq => false
  | _ => true

/--
Checks whether the ordering is `lt` or `eq`.
-/
def isLE : Ordering → Bool
  | gt => false
  | _ => true

/--
Checks whether the ordering is `lt`.
-/
def isLT : Ordering → Bool
  | lt => true
  | _ => false

/--
Checks whether the ordering is `gt`.
-/
def isGT : Ordering → Bool
  | gt => true
  | _ => false

/--
Checks whether the ordering is `gt` or `eq`.
-/
def isGE : Ordering → Bool
  | lt => false
  | _ => true

section Lemmas

@[simp]
theorem isLT_lt : lt.isLT := rfl

@[simp]
theorem isLE_lt : lt.isLE := rfl

@[simp]
theorem isEq_lt : lt.isEq = false := rfl

@[simp]
theorem isNe_lt : lt.isNe = true := rfl

@[simp]
theorem isGE_lt : lt.isGE = false := rfl

@[simp]
theorem isGT_lt : lt.isGT = false := rfl

@[simp]
theorem isLT_eq : eq.isLT = false := rfl

@[simp]
theorem isLE_eq : eq.isLE := rfl

@[simp]
theorem isEq_eq : eq.isEq := rfl

@[simp]
theorem isNe_eq : eq.isNe = false := rfl

@[simp]
theorem isGE_eq : eq.isGE := rfl

@[simp]
theorem isGT_eq : eq.isGT = false := rfl

@[simp]
theorem isLT_gt : gt.isLT = false := rfl

@[simp]
theorem isLE_gt : gt.isLE = false := rfl

@[simp]
theorem isEq_gt : gt.isEq = false := rfl

@[simp]
theorem isNe_gt : gt.isNe = true := rfl

@[simp]
theorem isGE_gt : gt.isGE := rfl

@[simp]
theorem isGT_gt : gt.isGT := rfl

@[simp]
theorem swap_lt : lt.swap = .gt := rfl

@[simp]
theorem swap_eq : eq.swap = .eq := rfl

@[simp]
theorem swap_gt : gt.swap = .lt := rfl

theorem eq_eq_of_isLE_of_isLE_swap {o : Ordering} : o.isLE → o.swap.isLE → o = .eq := by
  cases o <;> simp

theorem eq_eq_of_isGE_of_isGE_swap {o : Ordering} : o.isGE → o.swap.isGE → o = .eq := by
  cases o <;> simp

theorem eq_eq_of_isLE_of_isGE {o : Ordering} : o.isLE → o.isGE → o = .eq := by
  cases o <;> simp

theorem eq_swap_iff_eq_eq {o : Ordering} : o = o.swap ↔ o = .eq := by
  cases o <;> simp

theorem eq_eq_of_eq_swap {o : Ordering} : o = o.swap → o = .eq :=
  eq_swap_iff_eq_eq.mp

@[simp]
theorem isLE_eq_false {o : Ordering} : o.isLE = false ↔ o = .gt := by
  cases o <;> simp

@[simp]
theorem isGE_eq_false {o : Ordering} : o.isGE = false ↔ o = .lt := by
  cases o <;> simp

@[simp]
theorem swap_eq_gt {o : Ordering} : o.swap = .gt ↔ o = .lt := by
  cases o <;> simp

@[simp]
theorem swap_eq_lt {o : Ordering} : o.swap = .lt ↔ o = .gt := by
  cases o <;> simp

@[simp]
theorem swap_eq_eq {o : Ordering} : o.swap = .eq ↔ o = .eq := by
  cases o <;> simp

@[simp]
theorem isLT_swap {o : Ordering} : o.swap.isLT = o.isGT := by
  cases o <;> simp

@[simp]
theorem isLE_swap {o : Ordering} : o.swap.isLE = o.isGE := by
  cases o <;> simp

@[simp]
theorem isEq_swap {o : Ordering} : o.swap.isEq = o.isEq := by
  cases o <;> simp

@[simp]
theorem isNe_swap {o : Ordering} : o.swap.isNe = o.isNe := by
  cases o <;> simp

@[simp]
theorem isGE_swap {o : Ordering} : o.swap.isGE = o.isLE := by
  cases o <;> simp

@[simp]
theorem isGT_swap {o : Ordering} : o.swap.isGT = o.isLT := by
  cases o <;> simp

theorem isLT_iff_eq_lt {o : Ordering} : o.isLT ↔ o = .lt := by
  cases o <;> simp

theorem isLE_iff_eq_lt_or_eq_eq {o : Ordering} : o.isLE ↔ o = .lt ∨ o = .eq := by
  cases o <;> simp

theorem isLE_of_eq_lt {o : Ordering} : o = .lt → o.isLE := by
  rintro rfl; rfl

theorem isLE_of_eq_eq {o : Ordering} : o = .eq → o.isLE := by
  rintro rfl; rfl

theorem isEq_iff_eq_eq {o : Ordering} : o.isEq ↔ o = .eq := by
  cases o <;> simp

theorem isNe_iff_ne_eq {o : Ordering} : o.isNe ↔ o ≠ .eq := by
  cases o <;> simp

theorem isGE_iff_eq_gt_or_eq_eq {o : Ordering} : o.isGE ↔ o = .gt ∨ o = .eq := by
  cases o <;> simp

theorem isGE_of_eq_gt {o : Ordering} : o = .gt → o.isGE := by
  rintro rfl; rfl

theorem isGE_of_eq_eq {o : Ordering} : o = .eq → o.isGE := by
  rintro rfl; rfl

theorem isGT_iff_eq_gt {o : Ordering} : o.isGT ↔ o = .gt := by
  cases o <;> simp

@[simp]
theorem swap_swap {o : Ordering} : o.swap.swap = o := by
  cases o <;> simp

@[simp] theorem swap_inj {o₁ o₂ : Ordering} : o₁.swap = o₂.swap ↔ o₁ = o₂ :=
  ⟨fun h => by simpa using congrArg swap h, congrArg _⟩

theorem swap_then (o₁ o₂ : Ordering) : (o₁.then o₂).swap = o₁.swap.then o₂.swap := by
  cases o₁ <;> rfl

theorem then_eq_lt {o₁ o₂ : Ordering} : o₁.then o₂ = lt ↔ o₁ = lt ∨ o₁ = eq ∧ o₂ = lt := by
  cases o₁ <;> cases o₂ <;> decide

theorem then_eq_eq {o₁ o₂ : Ordering} : o₁.then o₂ = eq ↔ o₁ = eq ∧ o₂ = eq := by
  cases o₁ <;> simp [«then»]

theorem then_eq_gt {o₁ o₂ : Ordering} : o₁.then o₂ = gt ↔ o₁ = gt ∨ o₁ = eq ∧ o₂ = gt := by
  cases o₁ <;> cases o₂ <;> decide

end Lemmas

end Ordering

/--
Uses decidable less-than and equality relations to find an `Ordering`.

In particular, if `x < y` then the result is `Ordering.lt`. If `x = y` then the result is
`Ordering.eq`. Otherwise, it is `Ordering.gt`.

`compareOfLessAndBEq` uses `BEq` instead of `DecidableEq`.
-/
@[inline] def compareOfLessAndEq {α} (x y : α) [LT α] [Decidable (x < y)] [DecidableEq α] : Ordering :=
  if x < y then Ordering.lt
  else if x = y then Ordering.eq
  else Ordering.gt

/--
Uses a decidable less-than relation and Boolean equality to find an `Ordering`.

In particular, if `x < y` then the result is `Ordering.lt`. If `x == y` then the result is
`Ordering.eq`. Otherwise, it is `Ordering.gt`.

`compareOfLessAndEq` uses `DecidableEq` instead of `BEq`.
-/
@[inline] def compareOfLessAndBEq {α} (x y : α) [LT α] [Decidable (x < y)] [BEq α] : Ordering :=
  if x < y then .lt
  else if x == y then .eq
  else .gt

/--
Compares `a` and `b` lexicographically by `cmp₁` and `cmp₂`.

`a` and `b` are first compared by `cmp₁`. If this returns `Ordering.eq`, `a` and `b` are compared
by `cmp₂` to break the tie.

To lexicographically combine two `Ordering`s, use `Ordering.then`.
-/
@[inline] def compareLex (cmp₁ cmp₂ : α → β → Ordering) (a : α) (b : β) : Ordering :=
  (cmp₁ a b).then (cmp₂ a b)

/--
`Ord α` provides a computable total order on `α`, in terms of the
`compare : α → α → Ordering` function.

Typically instances will be transitive, reflexive, and antisymmetric,
but this is not enforced by the typeclass.

There is a derive handler, so appending `deriving Ord` to an inductive type or structure
will attempt to create an `Ord` instance.
-/
class Ord (α : Type u) where
  /-- Compare two elements in `α` using the comparator contained in an `[Ord α]` instance. -/
  compare : α → α → Ordering

export Ord (compare)

set_option linter.unusedVariables false in  -- allow specifying `ord` explicitly
/--
Compares two values by comparing the results of applying a function.

In particular, `x` is compared to `y` by comparing `f x` and `f y`.

Examples:
 * `compareOn (·.length) "apple" "banana" = .lt`
 * `compareOn (· % 3) 5 6 = .gt`
 * `compareOn (·.foldl max 0) [1, 2, 3] [3, 2, 1] = .eq`
-/
@[inline] def compareOn [ord : Ord β] (f : α → β) (x y : α) : Ordering :=
  compare (f x) (f y)

instance : Ord Nat where
  compare x y := compareOfLessAndEq x y

instance : Ord Int where
  compare x y := compareOfLessAndEq x y

instance : Ord Bool where
  compare
  | false, true => Ordering.lt
  | true, false => Ordering.gt
  | _, _ => Ordering.eq

instance : Ord String where
  compare x y := compareOfLessAndEq x y

instance (n : Nat) : Ord (Fin n) where
  compare x y := compare x.val y.val

instance : Ord UInt8 where
  compare x y := compareOfLessAndEq x y

instance : Ord UInt16 where
  compare x y := compareOfLessAndEq x y

instance : Ord UInt32 where
  compare x y := compareOfLessAndEq x y

instance : Ord UInt64 where
  compare x y := compareOfLessAndEq x y

instance : Ord USize where
  compare x y := compareOfLessAndEq x y

instance : Ord Char where
  compare x y := compareOfLessAndEq x y

instance [Ord α] : Ord (Option α) where
  compare
  | none,   none   => .eq
  | none,   some _ => .lt
  | some _, none   => .gt
  | some x, some y => compare x y

/-- The lexicographic order on pairs. -/
def lexOrd [Ord α] [Ord β] : Ord (α × β) where
  compare := compareLex (compareOn (·.1)) (compareOn (·.2))

/--
Constructs an `LT` instance from an `Ord` instance that asserts that the result of `compare` is
`Ordering.lt`.
-/
def ltOfOrd [Ord α] : LT α where
  lt a b := compare a b = Ordering.lt

instance [Ord α] : DecidableRel (@LT.lt α ltOfOrd) :=
  inferInstanceAs (DecidableRel (fun a b => compare a b = Ordering.lt))

/--
Constructs an `LT` instance from an `Ord` instance that asserts that the result of `compare`
satisfies `Ordering.isLE`.
-/
def leOfOrd [Ord α] : LE α where
  le a b := (compare a b).isLE

instance [Ord α] : DecidableRel (@LE.le α leOfOrd) :=
  inferInstanceAs (DecidableRel (fun a b => (compare a b).isLE))

namespace Ord

/--
Constructs a `BEq` instance from an `Ord` instance.
-/
protected def toBEq (ord : Ord α) : BEq α where
  beq x y := ord.compare x y == .eq

/--
Constructs an `LT` instance from an `Ord` instance.
-/
protected def toLT (ord : Ord α) : LT α :=
  ltOfOrd

instance [i : Ord α] : DecidableRel (@LT.lt _ (Ord.toLT i)) :=
  inferInstanceAs (DecidableRel (fun a b => compare a b = Ordering.lt))

/--
Constructs an `LE` instance from an `Ord` instance.
-/
protected def toLE (ord : Ord α) : LE α :=
  leOfOrd

instance [i : Ord α] : DecidableRel (@LE.le _ (Ord.toLE i)) :=
  inferInstanceAs (DecidableRel (fun a b => (compare a b).isLE))

/--
Inverts the order of an `Ord` instance.

The result is an `Ord α` instance that returns `Ordering.lt` when `ord` would return `Ordering.gt`
and that returns `Ordering.gt` when `ord` would return `Ordering.lt`.
-/
protected def opposite (ord : Ord α) : Ord α where
  compare x y := ord.compare y x

/--
Constructs an `Ord` instance that compares values according to the results of `f`.

In particular, `ord.on f` compares `x` and `y` by comparing `f x` and `f y` according to `ord`.

The function `compareOn` can be used to perform this comparison without constructing an intermediate
`Ord` instance.
-/
protected def on (_ : Ord β) (f : α → β) : Ord α where
  compare := compareOn f

/--
Constructs the lexicographic order on products `α × β` from orders for `α` and `β`.
-/
protected def lex (_ : Ord α) (_ : Ord β) : Ord (α × β) :=
  lexOrd

/--
Constructs an `Ord` instance from two existing instances by combining them lexicographically.

The resulting instance compares elements first by `ord₁` and then, if this returns `Ordering.eq`, by
`ord₂`.

The function `compareLex` can be used to perform this comparison without constructing an
intermediate `Ord` instance. `Ordering.then` can be used to lexicographically combine the results of
comparisons.
-/
protected def lex' (ord₁ ord₂ : Ord α) : Ord α where
  compare := compareLex ord₁.compare ord₂.compare

/--
Constructs an order which compares elements of an `Array` in lexicographic order.
-/
protected def arrayOrd [a : Ord α] : Ord (Array α) where
  compare x y :=
    let _ : LT α := a.toLT
    let _ : BEq α := a.toBEq
    if List.lex x.toList y.toList then .lt else if x == y then .eq else .gt

end Ord
