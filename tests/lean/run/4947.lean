universe u
class G (A : outParam Nat) where Z : Type u
export G (Z)
abbrev f (a : Nat) : Nat := 2 ^ a
variable [G (f 0)]
example {s : Z} : s = s := by simp only [Nat.reducePow]
