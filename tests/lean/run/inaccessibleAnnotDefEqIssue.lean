example : Int → Nat
| (_ : Nat)     => 0
| Int.negSucc n => 0

protected theorem Int.add_comm : ∀ a b : Int, a + b = b + a
| (n : Nat), (m : Nat)         => sorry
| (_ : Nat), Int.negSucc _     => rfl
| Int.negSucc _, (_ : Nat)     => rfl
| Int.negSucc _, Int.negSucc _ => sorry
