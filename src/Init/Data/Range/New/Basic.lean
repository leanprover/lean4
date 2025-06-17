module

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Iterators.Consumers
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

class SupportsLowerBound (shape : BoundShape) (α : Type u) where
  IsSatisfied : Bound shape α → α → Prop
  decidableSatisfiesLowerBound : DecidableRel IsSatisfied := by infer_instance

instance : SupportsLowerBound .unbounded α where
  IsSatisfied _ _ := True

class SupportsUpperBound (shape : BoundShape) (α : Type u) where
  IsSatisfied : Bound shape α → α → Prop
  decidableSatisfiesUpperBound : DecidableRel IsSatisfied := by infer_instance

instance : SupportsUpperBound .unbounded α where
  IsSatisfied _ _ := True

instance [i : SupportsLowerBound shape α] : DecidableRel i.IsSatisfied :=
  i.decidableSatisfiesLowerBound

instance [i : SupportsUpperBound shape α] : DecidableRel i.IsSatisfied :=
  i.decidableSatisfiesUpperBound

instance [SupportsLowerBound sl α] [SupportsUpperBound su α] :
    Membership α (PRange ⟨sl, su⟩ α) where
  mem r a := SupportsLowerBound.IsSatisfied r.lower a ∧ SupportsUpperBound.IsSatisfied r.upper a

instance [SupportsLowerBound sl α] [SupportsUpperBound su α] (r : PRange ⟨sl, su⟩ α) :
    Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (_ ∧ _)

class FinitelyEnumerableRange (shape α) [SupportsUpperBound shape α] where
  enumeration : Bound shape α → List α
  mem_enumeration_of_satisfiesUpperBound : (u : Bound shape α) → (a : α) →
    SupportsUpperBound.IsSatisfied u a → a ∈ enumeration u

class UpwardEnumerableRange (lowerBoundShape : BoundShape) (α : Type u) where
  init : Bound lowerBoundShape α → Option α

class LawfulUpwardEnumerableLowerBound (sl α) [UpwardEnumerable α]
    [SupportsLowerBound sl α] [UpwardEnumerableRange sl α] where
  isValid_iff (a : α) (l : Bound sl α) :
    SupportsLowerBound.IsSatisfied l a ↔
      ∃ init, UpwardEnumerableRange.init l = some init ∧ UpwardEnumerable.le init a

class LawfulUpwardEnumerableUpperBound (su α) [UpwardEnumerable α] [SupportsUpperBound su α] where
  isValid_of_le (u : Bound su α) (a b : α) :
    SupportsUpperBound.IsSatisfied u b → UpwardEnumerable.le a b → SupportsUpperBound.IsSatisfied u a

theorem LawfulUpwardEnumerableLowerBound.isValid_of_le [SupportsLowerBound sl α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [UpwardEnumerableRange sl α] [LawfulUpwardEnumerableLowerBound sl α]
    (l : Bound sl α) (a b : α)
    (ha : SupportsLowerBound.IsSatisfied l a) (hle : UpwardEnumerable.le a b) :
    SupportsLowerBound.IsSatisfied l b := by
  rw [LawfulUpwardEnumerableLowerBound.isValid_iff] at ⊢ ha
  obtain ⟨init, hi, ha⟩ := ha
  exact ⟨init, hi, UpwardEnumerable.le_trans ha hle⟩

instance [LT α] [DecidableLT α] : SupportsLowerBound .open α where
  IsSatisfied bound a := bound < a

instance [LT α] [DecidableLT α] : SupportsUpperBound .open α where
  IsSatisfied bound a := a < bound

instance [LE α] [DecidableLE α] : SupportsLowerBound .closed α where
  IsSatisfied bound a := bound ≤ a

instance [LE α] [DecidableLE α] : SupportsUpperBound .closed α where
  IsSatisfied bound a := a ≤ bound

instance [Least? α] : UpwardEnumerableRange .unbounded α where
  init _ := Least?.least?

instance [UpwardEnumerable α] : UpwardEnumerableRange .open α where
  init lower := UpwardEnumerable.succ? lower

instance : UpwardEnumerableRange .closed α where
  init lower := some lower
