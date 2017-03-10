def ex (a b c : nat) : a = b → c = b → a = c ∧ b = c :=
begin
  intros,
  split,
  abstract { transitivity, trace "hello", trace_state, assumption, symmetry, assumption },
  abstract { symmetry, assumption }
end

#print ex
