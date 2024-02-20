@[coe] def Bool.toNat' : Bool → Nat
  | true => 1
  | false => 0

instance : Coe Bool Nat where
  coe := Bool.toNat'

@[norm_cast] theorem ofNat_band (a b : Bool) : (↑(a && b) : Nat) = ↑a &&& ↑b := by
  cases a <;> cases b <;> rfl

example (a b c : Bool) (n : Nat) (h : n = a &&& b &&& c)
        : (↑(a && b && c) : Nat) = n := by
  push_cast
  guard_target =ₛ(↑a &&& ↑b &&& ↑c) = n
  rw [h]

example (a b c : Bool) (n : Nat) (h : n = (a && b && c))
        : (↑a &&& ↑b &&& ↑c) = n := by
  norm_cast
  guard_target =ₛ ↑(a && b && c) = n
  rw [h]
