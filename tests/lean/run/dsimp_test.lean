def f : nat → nat
| 0     := 10
| (n+1) := 20 + n

open list tactic

meta def check_expr (p : pexpr) (t : expr) : tactic unit :=
do e ← to_expr p, guard (t = e)

meta def check_target (p : pexpr) : tactic unit :=
do t ← target, check_expr p t

local attribute [-simp] map head

example (a b c : nat) : head (map f [1, 2, 3]) = 20 :=
begin
  dsimp [map],
  check_target `(head [f 1, f 2, f 3] = 20),
  dsimp [f],
  check_target `(head [20 + 0, 20 + 1,  20 + 2] = 20),
  dsimp [head],
  check_target `(20 + 0 = 20),
  reflexivity
end

example (a b c : nat) : head (map f [1, 2, 3]) = 20 :=
begin
  dsimp [map, f, head],
  check_target `(20 + 0 = 20),
  reflexivity
end

@[simp] lemma succ_zero_eq_one : nat.succ 0 = 1 :=
rfl

def g : nat × nat → nat
| (a, b) := a + b

lemma gax (x y) : g (x, y) = x + y :=
rfl

attribute [simp] gax

example (a b c : nat) : g (f 1, f 2) = 41 :=
begin
  dsimp,
  check_target `(f 1 + f 2 = 41),
  dsimp [f],
  reflexivity
end

example (a b c : nat) : g (f 1, f 2) = 41 :=
begin
  dsimp [f],
  check_target `(20 + 0 + (20 + 1) = 41),
  reflexivity
end

example (a b c : nat) : g (f 1, f 2) = 41 :=
begin
  dsimp [f] without gax,
  check_target `(g (20 + 0, 20 + 1) = 41),
  dsimp [g],
  check_target `(20 + 0 + (20 + 1) = 41),
  reflexivity
end

local attribute [-simp] gax

example (a b c : nat) : g (f 1, f 2) = 41 :=
begin
  dsimp [f],
  check_target `(g (20 + 0, 20 + 1) = 41),
  dsimp [gax],
  check_target `(20 + 0 + (20 + 1) = 41),
  reflexivity
end

example (a b c : nat) : g (f 1, f 2) = 41 :=
begin
  dsimp [f, gax],
  check_target `(20 + 0 + (20 + 1) = 41),
  reflexivity
end
