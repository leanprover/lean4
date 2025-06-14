module

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Iterators
import Init.Data.Range.New.Classes

open Std.Iterators

inductive BoundShape where
  | «open» : BoundShape
  | closed : BoundShape
  | unbounded : BoundShape

structure RangeShape where
  lower : BoundShape
  upper : BoundShape

abbrev Bound (shape : BoundShape) (α : Type u) : Type u :=
  match shape with
  | .open | .closed => α
  | .unbounded => PUnit

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
  | `($a,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.closed) $a $b)
  | `(,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.unbounded BoundShape.closed) PUnit.unit $b)
  | `($a,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.unbounded) $a PUnit.unit)
  | `(,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.unbounded BoundShape.unbounded) PUnit.unit PUnit.unit)
  | `($a<,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.closed) $a $b)
  | `($a<,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.unbounded) $a PUnit.unit)
  | `($a,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.open) $a $b)
  | `(,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.unbounded BoundShape.open) PUnit.unit $b)
  | `($a<,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.open) $a $b)

class HasRange (shape : RangeShape) (α : Type u) where
  SatisfiesLowerBound : Bound shape.lower α → α → Prop
  SatisfiesUpperBound : Bound shape.upper α → α → Prop
  decidableSatisfiesLowerBound : DecidableRel SatisfiesLowerBound := by infer_instance
  decidableSatisfiesUpperBound : DecidableRel SatisfiesUpperBound := by infer_instance

instance [i : HasRange shape α] : DecidableRel i.SatisfiesLowerBound :=
  i.decidableSatisfiesLowerBound

instance [i : HasRange shape α] : DecidableRel i.SatisfiesUpperBound :=
  i.decidableSatisfiesUpperBound

instance [HasRange shape α] : Membership α (PRange shape α) where
  mem r a := HasRange.SatisfiesLowerBound r.lower a ∧ HasRange.SatisfiesUpperBound r.upper a

instance [HasRange shape α] (r : PRange shape α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (_ ∧ _)

class UpwardEnumerableRange (shape : RangeShape) (α : Type u) where
  init : Bound shape.lower α → Option α

class LawfulUpwardEnumerableRange [HasRange shape α] [UpwardEnumerable α]
    [UpwardEnumerableRange shape α] where
  satisfiesUpperBound_of_le (u : Bound shape.upper α) (a b : α) :
    HasRange.SatisfiesUpperBound u b → UpwardEnumerable.le a b → HasRange.SatisfiesUpperBound u a
  mem_iff (a : α) (r : PRange shape α) :
    a ∈ r ↔ ∃ init, UpwardEnumerableRange.init r.lower = some init ∧ UpwardEnumerable.le init a ∧
        HasRange.SatisfiesUpperBound r.upper a

instance : HasRange ⟨.unbounded, .unbounded⟩ α where
  SatisfiesUpperBound _ _ := True
  SatisfiesLowerBound _ _ := True

instance [LT α] [DecidableLT α] : HasRange ⟨.unbounded, .open⟩ α where
  SatisfiesLowerBound _ _ := True
  SatisfiesUpperBound upper a := a < upper

instance [LE α] [DecidableLE α] : HasRange ⟨.unbounded, .closed⟩ α where
  SatisfiesLowerBound _ _ := True
  SatisfiesUpperBound upper a := a ≤ upper

instance [LT α] [DecidableLT α] : HasRange ⟨.open, .unbounded⟩ α where
  SatisfiesLowerBound lower a := lower < a
  SatisfiesUpperBound _ _ := True

instance [LT α] [DecidableLT α] : HasRange ⟨.open, .open⟩ α where
  SatisfiesLowerBound lower a := lower < a
  SatisfiesUpperBound upper a := a < upper

instance [LT α] [LE α] [DecidableLT α] [DecidableLE α] : HasRange ⟨.open, .closed⟩ α where
  SatisfiesLowerBound lower a := lower < a
  SatisfiesUpperBound upper a := a ≤ upper

instance [LE α] [DecidableLE α] : HasRange ⟨.closed, .unbounded⟩ α where
  SatisfiesLowerBound lower a := lower ≤ a
  SatisfiesUpperBound _ _ := True

instance [LE α] [LT α] [DecidableLE α] [DecidableLT α] : HasRange ⟨.closed, .open⟩ α where
  SatisfiesLowerBound lower a := lower ≤ a
  SatisfiesUpperBound upper a := a < upper

instance [LE α] [DecidableLE α] : HasRange ⟨.closed, .closed⟩ α where
  SatisfiesLowerBound lower a := lower ≤ a
  SatisfiesUpperBound upper a := a ≤ upper

instance [Least? α] : UpwardEnumerableRange ⟨.unbounded, upperShape⟩ α where
  init _ := Least?.least?

instance [UpwardEnumerable α] : UpwardEnumerableRange ⟨.open, upperShape⟩ α where
  init lower := UpwardEnumerable.succ? lower

instance : UpwardEnumerableRange ⟨.closed, upperShape⟩ α where
  init lower := some lower
