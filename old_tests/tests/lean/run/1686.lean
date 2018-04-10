def f (n : ℕ) := n + n
def g (n : ℕ) := 2*n

example (n : ℕ) : g (n+1) = f n + 2 :=
begin
 change 2 * (n + 1) = f n + 2,
 unfold f,
 guard_target 2 * (n + 1) = n + n + 2,
 admit
end

example (n : ℕ) : g (n+1) = f n + 2 :=
begin
 change g (n + 1) with 2 * (n+1),
 unfold f,
 guard_target 2 * (n + 1) = n + n + 2,
 admit
end

example (n : ℕ) : g (n+1) = f n + 2 :=
begin
 change 2 * (n + 1) = _,
 unfold f,
 guard_target 2 * (n + 1) = n + n + 2,
 admit
end
