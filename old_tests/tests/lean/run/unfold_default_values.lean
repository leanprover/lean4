structure S  :=
(x : nat)
(y : nat := 10)

example (a : nat) (h : 10 = a) : {S . x := 10}^.y = a :=
begin
  simp [S.y._default],
  guard_target 10 = a,
  exact h
end
