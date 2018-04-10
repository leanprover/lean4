def f (x : ℕ) := x

example : f 1 = 1 :=
let y := 2 in
begin
  dsimp [f] at *,
  guard_target 1 = 1,
  refl
end

example (α : Type) [has_add α] : f 1 = 1 :=
begin
  dsimp [f] at *,
  guard_target 1 = 1,
  refl
end
