example (x y z x' y' z': ℕ)  (h : (x, y, z) = (x', y', z')) : false :=
begin
  injection h,
  guard_hyp h_1 := x = x',
  guard_hyp h_2 := (y, z) = (y', z'),
  injection h_2,
  guard_hyp h_3 := y = y',
  guard_hyp h_4 := z = z',
  admit
end

example (x y z x' y' z': ℕ)  (h : (x, y, z) = (x', y', z')) : false :=
begin
  injections,
  guard_hyp h_1 := x = x',
  guard_hyp h_2 := (y, z) = (y', z'),
  guard_hyp h_3 := y = y',
  guard_hyp h_4 := z = z',
  admit
end
