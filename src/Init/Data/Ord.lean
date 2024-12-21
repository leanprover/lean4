/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian, Sebastian Ullrich
-/

prelude
import Init.Data.String
import Init.Data.Array.Basic

inductive Ordering where
  | lt | eq | gt
deriving Inhabited, BEq

namespace Ordering

deriving instance DecidableEq for Ordering

/-- Swaps less and greater ordering results -/
def swap : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

/--
If `o₁` and `o₂` are `Ordering`, then `o₁.then o₂` returns `o₁` unless it is `.eq`,
in which case it returns `o₂`. Additionally, it has "short-circuiting" semantics similar to
boolean `x && y`: if `o₁` is not `.eq` then the expression for `o₂` is not evaluated.
This is a useful primitive for constructing lexicographic comparator functions:
```
structure Person where
  name : String
  age : Nat

instance : Ord Person where
  compare a b := (compare a.name b.name).then (compare b.age a.age)
```
This example will sort people first by name (in ascending order) and will sort people with
the same name by age (in descending order). (If all fields are sorted ascending and in the same
order as they are listed in the structure, you can also use `deriving Ord` on the structure
definition for the same effect.)
-/
@[macro_inline] def «then» : Ordering → Ordering → Ordering
  | .eq, f => f
  | o, _ => o

/--
Check whether the ordering is 'equal'.
-/
def isEq : Ordering → Bool
  | eq => true
  | _ => false

/--
Check whether the ordering is 'not equal'.
-/
def isNe : Ordering → Bool
  | eq => false
  | _ => true

/--
Check whether the ordering is 'less than or equal to'.
-/
def isLE : Ordering → Bool
  | gt => false
  | _ => true

/--
Check whether the ordering is 'less than'.
-/
def isLT : Ordering → Bool
  | lt => true
  | _ => false

/--
Check whether the ordering is 'greater than'.
-/
def isGT : Ordering → Bool
  | gt => true
  | _ => false

/--
Check whether the ordering is 'greater than or equal'.
-/
def isGE : Ordering → Bool
  | lt => false
  | _ => true

end Ordering

/--
Yields an `Ordering` s.t. `x < y` corresponds to `Ordering.lt` / `Ordering.gt` and
`x = y` corresponds to `Ordering.eq`.
-/
@[inline] def compareOfLessAndEq {α} (x y : α) [LT α] [Decidable (x < y)] [DecidableEq α] : Ordering :=
  if x < y then Ordering.lt
  else if x = y then Ordering.eq
  else Ordering.gt

/--
Yields an `Ordering` s.t. `x < y` corresponds to `Ordering.lt` / `Ordering.gt` and
`x == y` corresponds to `Ordering.eq`.
-/
@[inline] def compareOfLessAndBEq {α} (x y : α) [LT α] [Decidable (x < y)] [BEq α] : Ordering :=
  if x < y then .lt
  else if x == y then .eq
  else .gt

/--
Compare `a` and `b` lexicographically by `cmp₁` and `cmp₂`. `a` and `b` are
first compared by `cmp₁`. If this returns 'equal', `a` and `b` are compared
by `cmp₂` to break the tie.
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
Compare `x` and `y` by comparing `f x` and `f y`.
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

def ltOfOrd [Ord α] : LT α where
  lt a b := compare a b = Ordering.lt

instance [Ord α] : DecidableRel (@LT.lt α ltOfOrd) :=
  inferInstanceAs (DecidableRel (fun a b => compare a b = Ordering.lt))

def leOfOrd [Ord α] : LE α where
  le a b := (compare a b).isLE

instance [Ord α] : DecidableRel (@LE.le α leOfOrd) :=
  inferInstanceAs (DecidableRel (fun a b => (compare a b).isLE))

namespace Ord

/--
Derive a `BEq` instance from an `Ord` instance.
-/
protected def toBEq (ord : Ord α) : BEq α where
  beq x y := ord.compare x y == .eq

/--
Derive an `LT` instance from an `Ord` instance.
-/
protected def toLT (_ : Ord α) : LT α :=
  ltOfOrd

instance [i : Ord α] : DecidableRel (@LT.lt _ (Ord.toLT i)) :=
  inferInstanceAs (DecidableRel (fun a b => compare a b = Ordering.lt))

/--
Derive an `LE` instance from an `Ord` instance.
-/
protected def toLE (_ : Ord α) : LE α :=
  leOfOrd

instance [i : Ord α] : DecidableRel (@LE.le _ (Ord.toLE i)) :=
  inferInstanceAs (DecidableRel (fun a b => (compare a b).isLE))

/--
Invert the order of an `Ord` instance.
-/
protected def opposite (ord : Ord α) : Ord α where
  compare x y := ord.compare y x

/--
`ord.on f` compares `x` and `y` by comparing `f x` and `f y` according to `ord`.
-/
protected def on (_ : Ord β) (f : α → β) : Ord α where
  compare := compareOn f

/--
Derive the lexicographic order on products `α × β` from orders for `α` and `β`.
-/
protected def lex (_ : Ord α) (_ : Ord β) : Ord (α × β) :=
  lexOrd

/--
Create an order which compares elements first by `ord₁` and then, if this
returns 'equal', by `ord₂`.
-/
protected def lex' (ord₁ ord₂ : Ord α) : Ord α where
  compare := compareLex ord₁.compare ord₂.compare

/--
Creates an order which compares elements of an `Array` in lexicographic order.
-/
protected def arrayOrd [a : Ord α] : Ord (Array α) where
  compare x y :=
    let _ : LT α := a.toLT
    let _ : BEq α := a.toBEq
    if List.lex x.toList y.toList then .lt else if x == y then .eq else .gt

end Ord
