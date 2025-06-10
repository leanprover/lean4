prelude
import Std.Data.Ranges.Basic
import Std.Data.Ranges.General
import Std.Data.Ranges.Slice
import Std.Data.Iterators.Combinators.Monadic.Lineage

open Std.Iterators

instance : Succ? Nat where
  succ? n := some (n + 1)

instance (stepSize : Nat) (h) :
    Finite (Range.SuccIterator (α := Nat) stepSize (· ≤ n) h) Id := by
  unfold Range.SuccIterator
  sorry

instance (stepSize : Nat) (h) :
    Finite (Range.SuccIterator (α := Nat) stepSize (· < n) h) Id := by
  unfold Range.SuccIterator
  sorry

instance (stepSize : Nat) (h) :
    IteratorSize (Range.SuccIterator (α := Nat) stepSize (· ≤ n) h) Id where
  size it := pure <| .up <| (n + stepSize - it.internalState.next) / stepSize

instance (stepSize : Nat) (h) :
    IteratorSizePartial (Range.SuccIterator (α := Nat) stepSize (· ≤ n) h) Id where
  size it := pure <| .up <| (n + stepSize - it.internalState.next) / stepSize

instance (stepSize : Nat) (h) :
    IteratorSize (Range.SuccIterator (α := Nat) stepSize (· < n) h) Id where
  size it := pure <| .up <| (n + stepSize - it.internalState.next - 1) / stepSize

instance (stepSize : Nat) (h) :
    IteratorSizePartial (Range.SuccIterator (α := Nat) stepSize (· < n) h) Id where
  size it := pure <| .up <| (n + stepSize - it.internalState.next - 1) / stepSize
