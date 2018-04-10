example (a b c : nat) : a = b → b = c → c = a :=
begin
  intro h1,
  intro h2,
  exact eq.symm (eq.trans h1 _),
end
