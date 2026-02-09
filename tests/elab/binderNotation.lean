#check ∃ x, x > 1
#check ∃ (x y : Nat), x > y
#check ∃ x y : Nat, x > y
#check ∃ (x : Nat) (y : Nat), x > y

theorem ex1 : (∃ x y : Nat, x > y) = (∃ (x : Nat) (y : Nat), x > y) := rfl

abbrev Vector' α n := { a : Array α // a.size = n }

#check Σ α n, Vector' α n
#check Σ (α : Type) (n : Nat), Vector' α n
#check (α : Type) × (n : Nat) × Vector' α n

#check Σ' α n, Vector' α n
#check Σ' (α : Type) (n : Nat), Vector' α n
#check (α : Type) ×' (n : Nat) ×' Vector' α n

#check @Vector'
#check fun (α : Type) => Sigma fun (n : Nat) => Vector' α n
