example (a b c : nat) (h₁ : a = b) (h₂ : b = c) : a = c :=
begin
  apply eq.trans _ h₂,
  -- the metavars created during elaboration become new goals
  trace_state,
  exact h₁
end

example (a : nat) : ∃ x, x = a :=
begin
  apply exists.intro,
  -- the goal for the witness should occur "after" the goal for x = a
  trace_state,
  refl
end

example (a : nat) : ∃ x, x = a :=
begin
  eapply exists.intro,
  -- only metavars with out forward dependencies are added as goals.
  trace_state,
  refl
end

example (a : nat) : ∃ x, x = a :=
begin
  fapply exists.intro,
  -- all unassigned metavars are added as new goals using the order they were created.
  trace_state,
  exact a,
  trace_state,
  refl
end
