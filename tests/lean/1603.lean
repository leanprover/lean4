def some_lets : ℕ → ℕ → ℕ
| 0            v := v
| (nat.succ n) v := let k := some_lets n v + v in k

def some_unfolded_lets (n : ℕ) : ∃ v : ℕ , v = some_lets 5 n :=
begin
  unfold some_lets,
  -- admit
end
