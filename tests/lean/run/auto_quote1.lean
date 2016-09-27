example (a b c : nat) : a = b → b = c → c = a :=
begin
  intros,
  apply eq.symm,
  apply eq.trans,
  assumption,
  assumption
end

example (a b c : nat) : a = b → b = c → c = a :=
begin
  intro h1,
  intro h2,
  refine eq.symm (eq.trans h1 _),
  exact h2
end

example (a b c : nat) : a = b → b = c → c = a :=
begin
  intros h1 h2, -- we can optionally provide the names
  refine eq.symm (eq.trans h1 _),
  exact h2
end

example (a b c : nat) : a = b → b = c → c = a :=
begin
  intro h1,
  intro, -- optional argument
  refine eq.symm (eq.trans h1 _),
  assumption
end

constant add_comm {a b : nat} : a + b = b + a
constant add_assoc {a b c : nat} : (a + b) + c = a + (b + c)
constant zero_add (a : nat) : 0 + a = a

example (a b c : nat) : b = 0 → 0 + a + b + c = c + a :=
begin
  intro h,
  rewrite h, -- single rewrite
  rewrite [zero_add, @add_comm a 0, zero_add, add_comm] -- sequence of rewrites
end

example (a b c : nat) : 0 = b → 0 + a + b + c = c + a :=
begin
  intro h,
  rewrite -h, -- single rewrite using symmetry
  rw [zero_add, @add_comm a 0, zero_add, add_comm] -- rw is shorthand for rewrite
end

open nat

example : ∀ n m : ℕ, n + m = m + n :=
begin
  intros n m,
  induction m with m' ih,
  { -- Remark: Used change here to make sure nat.zero is replaced with polymorphic zero.
    -- dsimp tactic should fix that in the future.
    change n + 0 = 0 + n, rw zero_add n },
  { change succ (n + m') = succ m' + n,
    rw [succ_add, ih] }
end
