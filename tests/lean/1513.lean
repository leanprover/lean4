example (n : ℕ) (h : n = 0) : n = 0 :=
by rename n m

example (n : ℕ) : let x := 10 in n > 0 → x > 5 → n ≠ x → x + 1 = 1 + x :=
begin
  intros,
  rename x y
end
