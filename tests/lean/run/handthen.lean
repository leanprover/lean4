open tactic

lemma ex1 (a b c : nat) : a + 0 = 0 + a ∧ b = b :=
begin
  -- We use `(` to go to regular tactic mode.
  constructor; [skip, constructor],
  -- Remaining goal is
  -- |- a + 0 = 0 + a
  simp
end

lemma ex2 (a b c : nat) : a + 0 = 0 + a ∧ b = b :=
begin
  constructor; [skip, constructor],
  simp
end

lemma ex3 (a b c : nat) : a + 0 = 0 + a ∧ b = b :=
begin
  /- We can use {} to group a sequence of tactics in the
        tac ; [tac_1, ..., tac_n]
     notation.
     However, a {} will not force the goal to be completely solved.
     Example:
     The first constructor tactic will produce two goals.
     The `;` combinator will apply the tactics {trace "Case1: ", trace_state} to the first goal and
     constructor to the second.
  -/
  constructor; [{trace "Case1: ", trace_state}, constructor],
  simp
end

lemma ex4 (a : nat) : a = a :=
begin
  /- We can use tac;[] to make sure that tac did not produce any goal -/
  refl; []
end
