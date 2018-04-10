open tactic

example (p q : Prop) : p → q → p ∧ q ∧ p :=
by do
  intros,
  c₁ ← return (expr.const `and.intro []),
  iterate_at_most 10 (apply c₁ >> skip <|> assumption)
