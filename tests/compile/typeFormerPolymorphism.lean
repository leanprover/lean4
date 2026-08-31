@[noinline]
def foo (α : Type 0) (β : Type 1) (f : α → β) (a : α) : α × β × (α → β) × (α → β) :=
  ⟨a, f a, f, f⟩

def alwaysNat (_ : Nat) : Type 0 := Nat

def main : IO Unit :=
  IO.println f!"{foo Nat (Type 0) alwaysNat 42 |>.1}"
