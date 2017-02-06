example (a b c : nat) : a = b → c = b → a = c ∧ b = c :=
begin
  intros,
  split,
  try {intro},    -- Should not report the error here
  repeat {intro}, -- Should not report the error here
  abstract { intro,  } -- Should report the error in intro tactic
end
