class Foo (α : Type) where
  decEq : DecidableEq α

instance instDecidableEq {α} [Foo α] : DecidableEq α := Foo.decEq
instance instFooNat : Foo Nat := ⟨by infer_instance⟩

def kron (i j : α) [DecidableEq α] : Nat := if (i=j) then 1 else 0

theorem kron_right_mul (α : Type) [foo : Foo α]  (i j : α) (x : Nat) : x * kron i j = kron i j * x := sorry

example {i j : Nat} : i * kron i j = kron i j * i := by
  rw [kron_right_mul]
