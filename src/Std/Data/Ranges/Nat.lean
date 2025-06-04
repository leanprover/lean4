prelude
import Std.Data.Ranges.Basic

open Std.Iterators

instance : RangeSize ⟨.closed, .closed⟩ Nat where
  size r := (r.upper + 1) - r.lower

instance : RangeSize ⟨.closed, .open⟩ Nat where
  size r := r.upper - r.lower

instance : RangeSize ⟨.open, .closed⟩ Nat where
  size r := r.upper - r.lower

instance : RangeSize ⟨.open, .open⟩ Nat where
  size r := r.upper - r.lower - 1

instance : RangeSize ⟨.none, .closed⟩ Nat where
  size r := r.upper + 1

instance : RangeSize ⟨.none, .open⟩ Nat where
  size r := r.upper

instance : RangeIter ⟨.closed, .closed⟩ Nat where
  State := _
  iter r := Iter.repeat (init := r.lower) (· + 1) |>.take r.size

instance : RangeIter ⟨.closed, .open⟩ Nat where
  State := _
  iter r := Iter.repeat (init := r.lower) (· + 1) |>.take r.size

instance : RangeIter ⟨.closed, .none⟩ Nat where
  State := _
  iter r := Iter.repeat (init := r.lower) (· + 1)

instance : RangeIter ⟨.open, .closed⟩ Nat where
  State := _
  iter r := Iter.repeat (init := r.lower) (· + 1) |>.take r.size

instance : RangeIter ⟨.open, .open⟩ Nat where
  State := _
  iter r := Iter.repeat (init := r.lower + 1) (· + 1) |>.take r.size

instance : RangeIter ⟨.open, .none⟩ Nat where
  State := _
  iter r := Iter.repeat (init := r.lower + 1) (· + 1)

instance : RangeIter ⟨.none, .closed⟩ Nat where
  State := _
  iter r := Iter.repeat (init := 0) (· + 1) |>.take r.size

instance : RangeIter ⟨.none, .open⟩ Nat where
  State := _
  iter r := Iter.repeat (init := 0) (· + 1) |>.take r.size

instance : RangeIter ⟨.none, .none⟩ Nat where
  State := _
  iter _ := Iter.repeat (init := 0) (· + 1)

instance : Membership Nat (PRange shape Nat) where
  mem r n := match shape with
    | ⟨sl, su⟩ => (match sl with
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

#eval (2,,5).iter.toList

#eval (,,<5).iter.toList

#eval 1 ∈ (1,,5)

def f : IO Unit := do
  for x in ((2 : Nat),,8) do -- ugly: For some reason, we need a type hint here
    IO.println x

#synth ForIn IO (type_of% (2,,8)) _ -- Note that we don't need the type hint this time
