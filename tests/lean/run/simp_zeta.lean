example (n : ℕ) : let m := 0 + n in m = n :=
begin
intro,
dsimp [m],
simp,
end

example (n : ℕ) : let m := 0 + n in m = n :=
begin
intro,
simp *,
end