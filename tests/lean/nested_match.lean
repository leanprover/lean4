namespace ex1

def f : ℕ → ℕ
| n :=
  (match n with
  | 0 := 0
  | (m+1) := f m
  end) + 1

def g  : ℕ → ℕ
| n :=
  (match n, rfl : ∀ m, m = n → ℕ with
  | 0,     h := 0
  | (m+1), h :=
    have m < n, begin rw [←h], apply nat.lt_succ_self end,
    g m
  end) + 1

end ex1

namespace ex2

mutual def f, g
with f : ℕ → ℕ
| n := g n + 1
with g : ℕ → ℕ
| 0 := 0
| (n+1) := f n

end ex2
