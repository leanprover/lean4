structure Foo (A B : Type) := f : Unit -> A
def foo (P : Type) : Foo ((p : P) -> Nat) ({p : P} -> Nat) := ⟨λ _ _ => 0⟩
def bar (P : Type) : Foo ((p : P) -> Nat) ({p : P} -> Int) := ⟨λ _ _ => 0⟩

#check foo Bool
#check (foo Bool).f -- (foo Bool).f : Unit → Bool → Nat
#check (bar Bool).f -- (bar Bool).f : Unit → Bool → Nat
