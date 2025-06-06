prelude
import Std.Data.Ranges.Basic
import Std.Data.Ranges.Slice
open Std.Iterators

-- Have: `LE`, `LT`, `HAdd`
-- Perhaps need: `Succ`
-- In general, how can we avoid cases like the zero step size?

class Succ? (α : Type u) where
  succ? : α → Option α
  succAtIdx? (n : Nat) (a : α) : Option α := Nat.repeat (· >>= succ?) n (some a)

instance : Membership α (PRange ⟨.none, .none⟩ α) where
  mem _ _ := True

instance (r : PRange ⟨.none, .none⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable True

instance [LT α] : Membership α (PRange ⟨.none, .open⟩ α) where
  mem r a := a < r.upper

instance [LT α] [DecidableLT α] (r : PRange ⟨.none, .open⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (a < r.upper)

instance [LE α] : Membership α (PRange ⟨.none, .closed⟩ α) where
  mem r a := a ≤ r.upper

instance [LE α] [DecidableLE α] (r : PRange ⟨.none, .closed⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (a ≤ r.upper)

instance [LT α] : Membership α (PRange ⟨.open, .none⟩ α) where
  mem r a := r.lower < a

instance [LT α] [DecidableLT α] (r : PRange ⟨.open, .none⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (r.lower < a)

instance [LT α] : Membership α (PRange ⟨.open, .open⟩ α) where
  mem r a := r.lower < a ∧ a < r.upper

instance [LT α] [DecidableLT α] (r : PRange ⟨.open, .open⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (r.lower < a ∧ _)

instance [LT α] [LE α] : Membership α (PRange ⟨.open, .closed⟩ α) where
  mem r a := r.lower < a ∧ a ≤ r.upper

instance [LT α] [DecidableLT α] [LE α] [DecidableLE α] (r : PRange ⟨.open, .closed⟩ α) :
    Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (_ ∧ _)

instance [LE α] : Membership α (PRange ⟨.closed, .none⟩ α) where
  mem r a := r.lower ≤ a

instance [LE α] [DecidableLE α] (r : PRange ⟨.closed, .none⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (r.lower ≤ a)

instance [LE α] [LT α] : Membership α (PRange ⟨.closed, .open⟩ α) where
  mem r a := r.lower ≤ a ∧ a < r.upper

instance [LT α] [DecidableLT α] [LE α] [DecidableLE α] (r : PRange ⟨.closed, .open⟩ α) :
    Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (_ ∧ _)

instance [LE α] : Membership α (PRange ⟨.closed, .closed⟩ α) where
  mem r a := r.lower ≤ a ∧ a ≤ r.upper

instance [LE α] [DecidableLE α] (r : PRange ⟨.closed, .closed⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (_ ∧ _)


section Iterator

def Range.succIteratorInternal [Succ? α] (init : α) (stepSize : Nat) (Predicate : α → Bool) :=
  Iter.repeatUntilNone (init := init) (Succ?.succAtIdx? stepSize) |>.takeWhile Predicate

def Range.SuccIterator [Succ? α] (stepSize : Nat) (Predicate : α → Bool)
    (_ : stepSize > 0) :=
  type_of% (succIteratorInternal (_ : α) stepSize Predicate).internalState

def Range.succIterator [Succ? α] (init : α) (stepSize : Nat) (Predicate : α → Bool) (h) :
    (Iter (α := SuccIterator stepSize Predicate h) α) :=
  Iter.repeatUntilNone (init := init) (Succ?.succAtIdx? stepSize) |>.takeWhile Predicate

instance [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
    Iterator (Range.SuccIterator stepSize Predicate h) Id α := by
  unfold Range.SuccIterator
  infer_instance

instance [Monad m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
    IteratorCollect (Range.SuccIterator stepSize Predicate h) Id m := by
  unfold Range.SuccIterator
  infer_instance

instance [Monad m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
    IteratorCollectPartial (Range.SuccIterator stepSize Predicate h) Id m := by
  unfold Range.SuccIterator
  infer_instance

instance [Monad m] [MonadLiftT Id m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
    IteratorLoop (Range.SuccIterator stepSize Predicate h) Id m := by
  unfold Range.SuccIterator
  infer_instance

instance [Monad m] [MonadLiftT Id m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
    IteratorLoopPartial (Range.SuccIterator stepSize Predicate h) Id m := by
  unfold Range.SuccIterator
  infer_instance

-- TODO: Should we hide the ≤ or < predicates behind some identifier to avoid accidental rewriting?
instance [Succ? α] [LE α] [DecidableLE α] : RangeIter ⟨.closed, .closed⟩ α :=
  .of fun r => Range.succIterator r.lower 1 (fun a => a ≤ r.upper) (by omega)

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.closed, .open⟩ α :=
  .of fun r => Range.succIterator r.lower 1 (fun a => a < r.upper) (by omega)

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.closed, .none⟩ α :=
  .of fun r => Range.succIterator r.lower 1 (fun _ => True) (by omega)

instance [Succ? α] [LE α] [DecidableLE α] : RangeIter ⟨.open, .closed⟩ α :=
  .of fun r => Range.succIterator r.lower 1 (fun a => a ≤ r.upper) (by omega) |>.drop 1

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.open, .open⟩ α :=
  .of fun r => Range.succIterator r.lower 1 (fun a => a < r.upper) (by omega) |>.drop 1

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.open, .none⟩ α :=
  .of fun r => Range.succIterator r.lower 1 (fun _ => True) (by omega) |>.drop 1

-- TODO: iterators for ranges that are unbounded downwards

end Iterator

section Examples

end Examples
