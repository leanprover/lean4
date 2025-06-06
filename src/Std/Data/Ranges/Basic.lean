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
  step : StepShape

abbrev Bound (shape : BoundShape) (α : Type u) : Type u :=
  match shape with
  | .open | .closed => α
  | .none => PUnit

abbrev StepSize (shape : StepShape.{u}) : Type u :=
  match shape with
  | .default => PUnit
  | .custom α => α

class HasRange (shape : RangeShape.{u}) (α : Type u) where
  IsValid : StepSize shape.step → Prop
  decidable : DecidablePred IsValid

instance [i : HasRange shape α] : DecidablePred i.IsValid :=
  i.decidable

structure PRange (shape : RangeShape.{u}) (α : Type u) [HasRange shape α] where
  lower : Bound shape.lower α
  upper : Bound shape.upper α
  step : StepSize shape.step
  valid : HasRange.IsValid α step

/-!

# Stepped ranges

- IP addresses (finite!), natural numbers, rational numbers

- backward, rational steps, continuous range without step indication,

-/

syntax:max (term ",," term) : term
syntax:max (",," term) : term
syntax:max (term ",,") : term
syntax:max (",,") : term
syntax:max (term "<,," term) : term
syntax:max (term "<,,") : term
syntax:max (term ",,<" term) : term
syntax:max (",,<" term) : term
syntax:max (term "<,,<" term) : term
syntax:max (term ",,→" term "→,," term) : term
-- syntax:max (",," term ",," term) : term
-- syntax:max (term ",," term ",,") : term
-- syntax:max (",," term ",,") : term
-- syntax:max (term "<,," term ",," term) : term
-- syntax:max (term "<,," term ",,") : term
-- syntax:max (term ",," term ",,<" term) : term
-- syntax:max (",," term ",,<" term) : term
-- syntax:max (term "<,," term ",,<" term) : term

macro_rules
  | `($a,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.closed StepShape.default) $a $b PUnit.unit (by decide))
  | `(,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.none BoundShape.closed StepShape.default) PUnit.unit $b PUnit.unit (by decide))
  | `($a,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.none StepShape.default) $a PUnit.unit PUnit.unit (by decide))
  | `(,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.none BoundShape.none StepShape.default) PUnit.unit PUnit.unit PUnit.unit (by decide))
  | `($a<,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.closed StepShape.default) $a $b PUnit.unit (by decide))
  | `($a<,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.none StepShape.default) $a PUnit.unit PUnit.unit (by decide))
  | `($a,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.open StepShape.default) $a $b PUnit.unit (by decide))
  | `(,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.none BoundShape.open StepShape.default) PUnit.unit $b PUnit.unit (by decide))
  | `($a<,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.open StepShape.default) $a $b PUnit.unit (by decide))
  | `($a,,→$s→,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.closed (StepShape.custom _)) $a $b $s (by decide))
  -- | `(,,$s,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.none BoundShape.closed StepShape.default) PUnit.unit $b)
  -- | `($a,,$s,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.none StepShape.default) $a PUnit.unit)
  -- | `(,,$s,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.none BoundShape.none StepShape.default) PUnit.unit PUnit.unit)
  -- | `($a<,,$s,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.closed StepShape.default) $a $b)
  -- | `($a<,,$s,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.none StepShape.default) $a PUnit.unit)
  -- | `($a,,$s,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.open StepShape.default) $a $b)
  -- | `(,,$s,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.none BoundShape.open StepShape.default) PUnit.unit $b)
  -- | `($a<,,$s,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.open StepShape.default) $a $b)

class RangeSize (shape : RangeShape) (α : Type u) [HasRange shape α] where
  size : PRange shape α → Nat

class RangeIter (shape : RangeShape) (α : Type u) [HasRange shape α] where
  State : PRange shape α → Type u
  iter : (r : PRange shape α) → Iter (α := State r) α

@[always_inline, inline]
def RangeIter.of [HasRange shape α] {State : PRange shape α → Type u}
    (iter : (r : PRange shape α) → Iter (α := State r) α) :
    RangeIter shape α where
  State := State
  iter := iter

instance [HasRange shape α] {State : PRange shape α → Type u}
    {r : PRange shape α} [Iterator (State r) Id α]
    {iter : (r : PRange shape α) → Iter (α := State r) α} :
    letI : RangeIter shape α := RangeIter.of iter
    Iterator (RangeIter.State (shape := shape) (α := α) r) Id α :=
  inferInstanceAs <| Iterator (State r) Id α

instance [HasRange shape α] {State : PRange shape α → Type u} {r : PRange shape α}
    [Iterator (State r) Id α]
    [Finite (State r) Id]
    {iter : (r : PRange shape α) → Iter (α := State r) α} :
    letI : RangeIter shape α := RangeIter.of iter
    Finite (RangeIter.State (shape := shape) (α := α) r) Id :=
  inferInstanceAs <| Finite (State r) Id

instance [HasRange shape α] {State : PRange shape α → Type u} {r : PRange shape α}
    [Iterator (State r) Id α] [IteratorCollect (State r) Id m]
    {iter : (r : PRange shape α) → Iter (α := State r) α} :
    letI : RangeIter shape α := RangeIter.of iter
    IteratorCollect (RangeIter.State r) Id m :=
  inferInstanceAs <| IteratorCollect (State r) Id m

@[always_inline, inline]
def PRange.size [HasRange shape α] [RangeSize shape α] (r : PRange shape α) : Nat :=
  RangeSize.size r

@[always_inline, inline]
def PRange.iter [HasRange shape α] [RangeIter shape α] (r : PRange shape α) :=
  (RangeIter.iter r : Iter α)

instance [HasRange shape α] [i : RangeIter shape α] [∀ r, ForIn m (Iter (α := i.State r) α) α] :
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
