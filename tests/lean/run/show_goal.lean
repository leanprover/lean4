open tactic

lemma ex (a b c : nat) : a + 0 = 0 + a ∧ 0 + b = b ∧ c + b = b + c :=
begin
  repeat {any_goals {constructor}},
  show_goal c + b = b + c, { apply add_comm },
  show_goal a + 0 = 0 + a, { simp },
  show_goal 0 + b = b,     { rw [zero_add] }
end
