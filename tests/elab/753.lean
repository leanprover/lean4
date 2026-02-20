inductive Val
| mk : Nat -> Val

instance : Inhabited Val where
default := Val.mk 0

@[simp]
theorem true_iff_true : True <-> True := Iff.intro (fun _ => trivial) (fun _ => trivial)
