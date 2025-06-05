prelude
import Std.Data.Ranges.Basic
import Std.Data.Ranges.Slice

open Std.Iterators

instance [RangeSize ⟨sl, su, .custom Nat⟩ Nat] : RangeSize ⟨sl, su, .default⟩ Nat where
  size r := (PRange.mk (shape := ⟨sl, su, .custom Nat⟩) r.lower r.upper 1).size

instance : RangeSize ⟨.closed, .closed, .custom Nat⟩ Nat where
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

instance : RangeIter ⟨.closed, .closed, .custom Nat⟩ Nat where
  State r := if r.step = 0 then _ else _
  iter r := if h : r.step = 0 then
      by rw [h]; exact Iter.repeat (init := r.lower) id
    else
      by rw [if_neg h]; exact Iter.repeat (init := r.lower) (· + r.step) |>.take r.size

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

#eval (2,,→2→,,10).iter.toList

#eval (,,<5).iter.toList

#eval 1 ∈ (1,,5)

#eval 1 ∈ (1,,→2→,,5)

def f : IO Unit := do
  for x in ((2 : Nat),,8) do -- ugly: For some reason, we need a type hint here
    IO.println x

#synth ForIn IO (type_of% (2,,8)) _ -- Note that we don't need the type hint this time

-- Slices


instance : Sliceable shape (Array α) Nat α where

instance : SliceIter ⟨.none, .none⟩ (Array α) Nat :=
  .of (·.collection.iter)

instance : SliceIter ⟨.closed, .none⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.drop s.range.lower)

instance : SliceIter ⟨.open, .none⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.drop (s.range.lower + 1))

instance : SliceIter ⟨.none, .closed⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take (s.range.upper + 1))

instance : SliceIter ⟨.closed, .closed⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take (s.range.upper + 1) |>.drop s.range.lower)

instance : SliceIter ⟨.open, .closed⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take (s.range.upper + 1) |>.drop (s.range.lower + 1))

instance : SliceIter ⟨.none, .open⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take s.range.upper)

instance : SliceIter ⟨.closed, .open⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take s.range.upper |>.drop s.range.lower)

instance : SliceIter ⟨.open, .open⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take s.range.upper |>.drop (s.range.lower + 1))

def testArray := (0,,<10).iter.toArray

#eval testArray[[2<,,]].iter.toList
