prelude
import Std.Data.Ranges.Basic
import Std.Data.Ranges.Slice
import Std.Data.Iterators.Combinators.Monadic.Lineage

open Std.Iterators

instance : HasRange ⟨sl, su, .custom Nat⟩ Nat where
  IsValid step := step > 0
  decidable := inferInstance

instance : HasRange ⟨sl, su, .default⟩ Nat where
  IsValid _ := True
  decidable := inferInstance



instance [RangeSize ⟨sl, su, .custom Nat⟩ Nat] : RangeSize ⟨sl, su, .default⟩ Nat where
  size r := (PRange.mk (shape := ⟨sl, su, .custom Nat⟩) r.lower r.upper 1 (by simp only [HasRange.IsValid]; omega; dsimp [RangeShape.step.eq_def]; decide)).size

instance [RangeSize ⟨.closed, .open, .custom Nat⟩ Nat] : RangeSize ⟨.closed, .open, .default⟩ Nat where
  size r := (PRange.mk (shape := ⟨.closed, .open, .custom Nat⟩) r.lower r.upper 1 (by decide)).size

instance [RangeSize ⟨.closed, .none, .custom Nat⟩ Nat] : RangeSize ⟨.closed, .none, .default⟩ Nat where
  size r := (PRange.mk (shape := ⟨.closed, .none, .custom Nat⟩) r.lower .unit 1 (by decide)).size

instance [RangeSize ⟨.open, .closed, .custom Nat⟩ Nat] : RangeSize ⟨.open, .closed, .default⟩ Nat where
  size r := (PRange.mk (shape := ⟨.open, .closed, .custom Nat⟩) r.lower r.upper 1 (by decide)).size

instance [RangeSize ⟨.open, .open, .custom Nat⟩ Nat] : RangeSize ⟨.open, .open, .default⟩ Nat where
  size r := (PRange.mk (shape := ⟨.open, .open, .custom Nat⟩) r.lower r.upper 1 (by decide)).size

instance [RangeSize ⟨.open, .none, .custom Nat⟩ Nat] : RangeSize ⟨.open, .none, .default⟩ Nat where
  size r := (PRange.mk (shape := ⟨.open, .none, .custom Nat⟩) r.lower .unit 1 (by decide)).size

instance [RangeSize ⟨.none, .closed, .custom Nat⟩ Nat] : RangeSize ⟨.none, .closed, .default⟩ Nat where
  size r := (PRange.mk (shape := ⟨.none, .closed, .custom Nat⟩) .unit r.upper 1 (by decide)).size

instance [RangeSize ⟨.none, .open, .custom Nat⟩ Nat] : RangeSize ⟨.none, .open, .default⟩ Nat where
  size r := (PRange.mk (shape := ⟨.none, .open, .custom Nat⟩) .unit r.upper 1 (by decide)).size

instance [RangeSize ⟨.none, .none, .custom Nat⟩ Nat] : RangeSize ⟨.none, .none, .default⟩ Nat where
  size r := (PRange.mk (α := Nat) (shape := ⟨.none, .none, .custom Nat⟩) .unit .unit 1 (by decide)).size

instance : RangeSize ⟨.none, .none, .custom Nat⟩ Nat where
  size r := ((r.upper + r.step) - r.lower) / r.step

instance : RangeSize ⟨.closed, .open, .custom Nat⟩ Nat where
  size r := (r.upper + r.step - r.lower - 1) / r.step

instance : RangeSize ⟨.open, .closed, .custom Nat⟩ Nat where
  size r := (r.upper + r.step - r.lower - 1) / r.step

instance : RangeSize ⟨.open, .open, .custom Nat⟩ Nat where
  size r := (r.upper + r.step - r.lower - 2) / r.step

instance : RangeSize ⟨.none, .closed, .custom Nat⟩ Nat where
  size r := (r.upper + r.step) / r.step

instance : RangeSize ⟨.none, .open, .custom Nat⟩ Nat where
  size r := (r.upper + r.step - 1) / r.step

instance [RangeIter ⟨sl, su, .custom Nat⟩ Nat] : RangeIter ⟨sl, su, .default⟩ Nat :=
  .of fun r => (PRange.mk (shape := ⟨sl, su, .custom Nat⟩) r.lower r.upper 1).iter

instance : RangeIter ⟨.closed, .closed, .custom Nat⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower) (· + r.step) |>.take r.size

instance : RangeIter ⟨.closed, .open, .custom Nat⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower) (· + r.step) |>.take r.size

instance : RangeIter ⟨.closed, .none, .custom Nat⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower) (· + r.step)

instance : RangeIter ⟨.open, .closed, .custom Nat⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower) (· + r.step) |>.take r.size

instance : RangeIter ⟨.open, .open, .custom Nat⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower + 1) (· + r.step) |>.take r.size

instance : RangeIter ⟨.open, .none, .custom Nat⟩ Nat :=
  .of fun r => Iter.repeat (init := r.lower + 1) (· + r.step)

instance : RangeIter ⟨.none, .closed, .custom Nat⟩ Nat :=
  .of fun r => Iter.repeat (init := 0) (· + r.step) |>.take r.size

instance : RangeIter ⟨.none, .open, .custom Nat⟩ Nat :=
  .of fun r => Iter.repeat (init := 0) (· + r.step) |>.take r.size

instance : RangeIter ⟨.none, .none, .custom Nat⟩ Nat :=
  .of fun r => Iter.repeat (init := 0) (· + r.step)

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
