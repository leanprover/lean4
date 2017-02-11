example (a b c : nat) : a = b → b = c → c = a :=
by {
  intros,
  apply eq.symm,
  apply eq.trans,
  assumption,
  assumption
}

example (a b c : nat) : a = b → b = c → c = a :=
by intros; apply eq.symm; apply eq.trans; repeat {assumption}

example (p q r : Prop) : p → q → r → p ∧ q ∧ r ∧ p ∧ q :=
by intros; repeat {assumption <|> constructor}
