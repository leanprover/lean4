prelude
import Std.Data.Ranges.Basic
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

instance : RangeIter ⟨.closed, .closed⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower) (· + 1) |>.take r.size

instance : RangeIter ⟨.closed, .open⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower) (· + 1) |>.take r.size

instance : RangeIter ⟨.closed, .none⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower) (· + 1)

instance : RangeIter ⟨.open, .closed⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower) (· + 1) |>.take r.size

instance : RangeIter ⟨.open, .open⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower + 1) (· + 1) |>.take r.size

instance : RangeIter ⟨.open, .none⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower + 1) (· + 1)

instance : RangeIter ⟨.none, .closed⟩ Nat :=
  .of fun r => Iter.repeat (init := 0) (· + 1) |>.take r.size

instance : RangeIter ⟨.none, .open⟩ Nat :=
  .of fun r => Iter.repeat (init := 0) (· + 1) |>.take r.size

instance : RangeIter ⟨.none, .none⟩ Nat :=
  .of fun r => Iter.repeat (init := 0) (· + 1)

instance : Membership Nat (PRange shape Nat) where
  mem r n := match shape with
    | ⟨sl, su, ss⟩ => (match sl with
        | .open => r.lower < n
        | .closed => r.lower ≤ n
        | .none => True) ∧
      (match su with
        | .open => n < r.upper
        | .closed => n ≤ r.upper
        | .none => True)

instance {n : Nat} {r : PRange shape Nat} : Decidable (n ∈ r) := by
  simp only [Membership.mem]
  split <;> split <;> infer_instance

#eval (2<,,<5).size

#eval (2,,→0→,,10).iter.toList

#eval (,,<5).iter.toList

#eval 1 ∈ (1,,5)

#eval 1 ∈ (1,,→2→,,5)

def f : IO Unit := do
  for x in ((2 : Nat),,8) do -- ugly: For some reason, we need a type hint here
    IO.println x

#synth ForIn IO (type_of% (2,,8)) _ -- Note that we don't need the type hint this time

-- Slices


instance : Sliceable shape (Array α) Nat α where

instance [i : SliceIter ⟨sl, su, .custom Nat⟩ (Array α) Nat] : SliceIter ⟨sl, su, .default⟩ (Array α) Nat where
  State s := i.State ⟨s.collection, ⟨s.range.lower, s.range.upper, 1⟩⟩
  iter s := i.iter ⟨s.collection, ⟨s.range.lower, s.range.upper, 1⟩⟩

instance : SliceIter ⟨.none, .none, .default⟩ (Array α) Nat :=
  .of (·.collection.iter)

instance : SliceIter ⟨.closed, .none, .default⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.drop s.range.lower)

instance : SliceIter ⟨.open, .none, .default⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.drop (s.range.lower + 1))

instance : SliceIter ⟨.none, .closed, .default⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take (s.range.upper + 1))

instance : SliceIter ⟨.closed, .closed, .default⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take (s.range.upper + 1) |>.drop s.range.lower)

instance : SliceIter ⟨.open, .closed, .default⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take (s.range.upper + 1) |>.drop (s.range.lower + 1))

instance : SliceIter ⟨.none, .open, .default⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take s.range.upper)

instance : SliceIter ⟨.closed, .open, .default⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take s.range.upper |>.drop s.range.lower)

instance : SliceIter ⟨.open, .open, .default⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take s.range.upper |>.drop (s.range.lower + 1))

def testArray := (0,,<10).iter.toArray

#eval testArray[[2<,,]].iter.toList
