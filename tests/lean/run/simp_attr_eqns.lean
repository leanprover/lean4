open nat tactic

meta def check_expr (p : pexpr) (t : expr) : tactic unit :=
do e ← to_expr p, guard (t = e)

meta def check_target (p : pexpr) : tactic unit :=
do t ← target, check_expr p t

def g : nat → nat → nat :=
λ x y, x * y

def f : nat → nat
| 0        := 10
| (succ a) := g (f a) 2

lemma ex0 (b a : nat) : b = f a → f (succ (succ a)) = g (g b 2) 2 :=
begin
  intro h,
  simp [f],
  check_target `(g (g (f a) 2) 2 = g (g b 2) 2),
  subst b
end

attribute [simp] f

lemma ex1 (b a : nat) : b = f a → f (succ a) = g b 2 :=
begin
  intro h,
  simp,
  check_target `(g (f a) 2 = g b 2),
  subst b
end

lemma ex2 (b a : nat) : b = f a → f (succ (succ a)) = g (g b 2) 2 :=
begin
  intro h,
  simp,
  check_target `(g (g (f a) 2) 2 = g (g b 2) 2),
  subst b
end

local attribute [-simp] f

lemma ex3 (b a : nat) : b = f a → f (succ a) = g b 2 :=
begin
  intro h,
  fail_if_success simp,
  subst b,
  reflexivity
end

run_command mk_simp_attr `mysimp

attribute [mysimp] f

lemma ex4 (b a : nat) : b = f a → f (succ a) = g b 2 :=
begin
  intro h,
  simp with mysimp,
  check_target `(g (f a) 2 = g b 2),
  subst b
end
