open nat tactic

def g : nat → nat → nat :=
λ x y, x * y

def f : nat → nat
| 0        := 10
| (succ a) := g (f a) 2

lemma ex0 (b a : nat) : b = f a → f (succ (succ a)) = g (g b 2) 2 :=
begin
  intro h,
  simp [f],
  guard_target g (g (f a) 2) 2 = g (g b 2) 2,
  subst b
end

attribute [simp] f

lemma ex1 (b a : nat) : b = f a → f (succ a) = g b 2 :=
begin
  intro h,
  simp,
  guard_target g (f a) 2 = g b 2,
  subst b
end

lemma ex2 (b a : nat) : b = f a → f (succ (succ a)) = g (g b 2) 2 :=
begin
  intro h,
  simp,
  guard_target g (g (f a) 2) 2 = g (g b 2) 2,
  subst b
end

local attribute [-simp] f

lemma ex3 (b a : nat) : b = f a → f (succ a) = g b 2 :=
begin
  intro h,
  fail_if_success {simp},
  subst b,
  reflexivity
end

run_cmd mk_simp_attr `mysimp

attribute [mysimp] f

lemma ex4 (b a : nat) : b = f a → f (succ a) = g b 2 :=
begin
  intro h,
  simp with mysimp,
  guard_target g (f a) 2 = g b 2,
  subst b
end
