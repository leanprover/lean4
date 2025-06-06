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

#eval "b" ∈ ("a",,"c")

#eval "a"

#eval! (1<,,<4).iter.toList

#eval (2<,,<5).size

-- #eval (,,<5).iter.toList

#eval 1 ∈ (1,,5)

-- TODO:
instance [Pure m] : MonadLiftT Id m where
  monadLift := pure

def f : IO Unit := do
  for x in ((2 : Nat),,8) do -- ugly: For some reason, we need a type hint here
    IO.println x

#synth ForIn IO (type_of% (2,,8)) _ -- Note that we don't need the type hint this time
