prelude
import Init.Core
import Init.NotationExtra
import Std.Data.Iterators
import Init.System.IO -- just for testing

open Std.Iterators

inductive BoundShape where
  | «open» : BoundShape
  | closed : BoundShape
  | none : BoundShape

inductive StepShape.{u} where
  | default : StepShape
  | custom : Type u → StepShape

structure RangeShape where
  lower : BoundShape
  upper : BoundShape

abbrev Bound (shape : BoundShape) (α : Type u) : Type u :=
  match shape with
  | .open | .closed => α
  | .none => PUnit

structure PRange (shape : RangeShape) (α : Type u) where
  lower : Bound shape.lower α
  upper : Bound shape.upper α

syntax:max (term ",," term) : term
syntax:max (",," term) : term
syntax:max (term ",,") : term
syntax:max (",,") : term
syntax:max (term "<,," term) : term
syntax:max (term "<,,") : term
syntax:max (term ",,<" term) : term
syntax:max (",,<" term) : term
syntax:max (term "<,,<" term) : term

macro_rules
  | `($a,,$b) => `(PRange.mk (shape := RangeShape.mk .closed .closed) $a $b)
  | `(,,$b) => `(PRange.mk (shape := RangeShape.mk .none .closed) .unit $b)
  | `($a,,) => `(PRange.mk (shape := RangeShape.mk .closed .none) $a .unit)
  | `(,,) => `(PRange.mk (shape := RangeShape.mk .none .none) .unit .unit)
  | `($a<,,$b) => `(PRange.mk (shape := RangeShape.mk .open .closed) $a $b)
  | `($a<,,) => `(PRange.mk (shape := RangeShape.mk .open .none) $a .unit)
  | `($a,,<$b) => `(PRange.mk (shape := RangeShape.mk .closed .open) $a $b)
  | `(,,<$b) => `(PRange.mk (shape := RangeShape.mk .none .open) .unit $b)
  | `($a<,,<$b) => `(PRange.mk (shape := RangeShape.mk .open .open) $a $b)

class RangeSize (shape : RangeShape) (α : Type u) where
  size : PRange shape α → Nat

/--
Always use `RangeIter.of` to create instances: Otherwise, no iterator-related
instances will be inferred for `RangeIter.State`.
-/
class RangeIter (shape : RangeShape) (α : Type u) where
  State : Type u
  iter : PRange shape α → Iter (α := State) α

@[always_inline, inline]
def RangeIter.of {State} (iter : PRange shape α → Iter (α := State) α) : RangeIter shape α where
  State := State
  iter := iter

instance [Iterator State Id α] {iter : PRange shape α → Iter (α := State) α} :
    letI : RangeIter shape α := RangeIter.of iter
    Iterator (RangeIter.State shape α) Id α :=
  inferInstanceAs <| Iterator State Id α

instance [Iterator State Id α] [Finite State Id]
    {iter : PRange shape α → Iter (α := State) α} :
    letI : RangeIter shape α := RangeIter.of iter
    Finite (RangeIter.State shape α) Id :=
  inferInstanceAs <| Finite State Id

instance [Iterator State Id α] [IteratorCollect State Id m]
    {iter : PRange shape α → Iter (α := State) α} :
    letI : RangeIter shape α := RangeIter.of iter
    IteratorCollect (RangeIter.State shape α) Id m :=
  inferInstanceAs <| IteratorCollect State Id m

@[always_inline, inline]
def PRange.size [RangeSize shape α] (r : PRange shape α) : Nat :=
  RangeSize.size r

@[always_inline, inline]
def PRange.iter [RangeIter shape α] (r : PRange shape α) :=
  (RangeIter.iter r : Iter α)

instance [i : RangeIter shape α] [ForIn m (Iter (α := i.State) α) α] :
    ForIn m (PRange shape α) α where
  forIn r := forIn r.iter

/-!

Ranges don't have a concept of orientation or steps.

They can support:

* size
* Membership
* toIter (possibly with an orientation/step size)
* getElem
* ForIn (via toIter? How to ensure termination? -> by encoding the bound shapes in the iterator type)

Slices: similar contexts but separate framework for performance reasons?

Actually, slices seem like the more fundamental concept.

Should slices always be allowed, possibly truncating, or not?
* List/Array: requiring proof seems sensible
* HashMap/TreeMap: any slices should be possible

# Use cases

`0..10` (`Nat`, `Int`, `Fin`, `ℝ`)

`0..10 (step := 3)`

`0.2..0.6 (step := 0.1)`

`xs[(0..1), (4..5)]` or `xs[(0, 4)..(1, 5)]`

`xs [10..0 (step := -2)]`

-/
