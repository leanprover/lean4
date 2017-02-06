example (a b c : nat) : a = b → c = b → a = c ∧ b = c :=
begin
  intros,
  split,
  try { transitivity, trace "hello", assumption, symmetry, assumption },
  abstract { symmetry, trace "test", assumption }
end
