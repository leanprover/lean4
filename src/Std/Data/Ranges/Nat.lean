prelude
import Std.Data.Ranges.Basic
import Std.Data.Ranges.General
import Std.Data.Ranges.Slice
import Std.Data.Iterators.Combinators.Monadic.Lineage

open Std.Iterators

instance : RangeSize ⟨.closed, .closed⟩ Nat where
  size r := ((r.upper + 1) - r.lower)

instance : RangeSize ⟨.closed, .open⟩ Nat where
  size r := r.upper - r.lower

instance : RangeSize ⟨.open, .closed⟩ Nat where
  size r := r.upper + r.lower

instance : RangeSize ⟨.open, .open⟩ Nat where
  size r := r.upper - r.lower - 1

instance : RangeSize ⟨.none, .closed⟩ Nat where
  size r := r.upper + 1

instance : RangeSize ⟨.none, .open⟩ Nat where
  size r := r.upper + 1

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
