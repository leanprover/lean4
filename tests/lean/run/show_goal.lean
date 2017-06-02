open tactic

lemma ex1 (a b c : nat) : a + 0 = 0 + a ∧ 0 + b = b ∧ c + b = b + c :=
begin
  repeat {any_goals {constructor}},
  show_goal c + b = b + c, { apply add_comm },
  show_goal a + 0 = 0 + a, { simp },
  show_goal 0 + b = b,     { rw [zero_add] }
end

lemma ex2 (a b c : nat) : a + 0 = 0 + a ∧ 0 + b = b ∧ c + b = b + c :=
begin
  repeat {any_goals {constructor}},
  show c + b = b + c, { apply add_comm },
  show a + 0 = 0 + a, { simp },
  show 0 + b = b,     { rw [zero_add] }
end

/- Same example, but the local context of each goal is different -/
lemma ex3 : (∀ a : nat, a + 0 = 0 + a) ∧ (∀ b : nat, 0 + b = b) ∧ (∀ b c : nat, c + b = b + c) :=
begin
  repeat {any_goals {constructor}}, all_goals {intros},
  show c + b = b + c, { apply add_comm },
  show a + 0 = 0 + a, { simp },
  show 0 + b = b,     { rw [zero_add] }
end
