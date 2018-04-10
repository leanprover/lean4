set_option trace.smt.ematch true

example (a b c d : nat) (f : nat → nat) : f d = a + b → f d - a + c = c + b :=
begin [smt]
  intros,
  eblast
end

example (a b c d : nat) (f : nat → nat) : f d = a + b → f d - (a + c) = b - c :=
begin [smt]
  intros,
  eblast
end
