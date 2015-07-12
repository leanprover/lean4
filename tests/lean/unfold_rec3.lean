open nat

definition nrec [recursor] := @nat.rec

definition myadd x y :=
nrec y (λ n r, succ r) x

theorem myadd_zero : ∀ n, myadd n 0 = n :=
begin
  intro n, induction n with n ih,
  reflexivity,
  esimp [myadd],
  state,
  rewrite ih
end
