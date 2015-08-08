open nat

tactic_notation T1 `:`:15 T2 := tactic.focus (tactic.and_then T1 (tactic.all_goals T2))

example (P Q : ℕ → ℕ → Prop) (n m : ℕ) (p : P n m) : Q n m ∧ false :=
begin
  split,
  revert m p, induction n : intro m; induction m : intro p,
  state, repeat exact sorry
end
