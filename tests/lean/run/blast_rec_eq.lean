open nat

lemma addz [simp] : ∀ a : nat, a + 0 = a := sorry
lemma zadd [simp] : ∀ a : nat, 0 + a = a := sorry
lemma adds [simp] : ∀ a b : nat, a + succ b = succ (a + b) := sorry
lemma sadd [simp] : ∀ a b : nat, succ a + b = succ (a + b) := sorry

definition comm : ∀ a b : nat, a + b = b + a
| a        0        := by simp
| a        (succ n) :=
  assert a + n = n + a, from !comm,
  by simp
