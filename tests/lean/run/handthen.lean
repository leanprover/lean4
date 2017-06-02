open tactic

lemma ex (a b c : nat) : a + 0 = 0 + a ∧ b = b :=
begin
  (constructor; [skip, constructor]),
  -- Remaining goal is
  -- |- a + 0 = 0 + a
  simp
end
