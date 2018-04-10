constant addc {a b : nat} : a + b = b + a
constant addassoc {a b c : nat} : (a + b) + c = a + (b + c)
constant zadd (a : nat) : 0 + a = a

open nat

example : ∀ n m : ℕ, n + m = m + n :=
begin
  intros n m,
  induction m with m' ih,
                      --^ "command": "info"
    { change n + 0 = 0 + n, simp [zadd] },
--^ "command": "info"
  { change succ (n + m') = succ m' + n,
    rw [succ_add, ih]
--^ "command":"info"
  }
end

example : ∀ n m : ℕ, n + m = m + n :=
begin
  intros n m,
  induction m with m' ih,
  {   change n + 0 = 0 + n, simp [zadd] },
   --^ "command": "info"
  { change succ (n + m') = succ m' + n,
    rw [succ_add, ih]
  }
end

example : ∀ n m : ℕ, n + m = m + n :=
begin
  intros n m,
  induction m with m' ih,
  {   change n + 0 = 0 + n, simp [zadd] },
                                      --^ "command": "info"
  { change succ (n + m') = succ m' + n,
    rw [succ_add, ih]
  }
end
