example (a b : nat) (h : a == b) : a + 1 = b + 1 :=
begin
  subst h
end

example (a b : nat) (h : a == b) : a + 1 = b + 1 :=
begin
  subst_vars
end
