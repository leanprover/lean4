def some_lets : ℕ → ℕ → ℕ
| 0            v := v
| (nat.succ n) v := let k := some_lets n v + some_lets n v in some_lets n k

def some_unfolded_lets (n : ℕ) : Σ' v : ℕ , v = some_lets 5 n :=
begin
  econstructor; unfold some_lets; econstructor
end

meta def foo : tactic unit :=
  do [g] <- tactic.get_goals,
     tactic.to_expr (``(1)) >>= tactic.unify g
def some_lifted_lets (n : ℕ) : Σ' (v : ℕ), v = psigma.fst (some_unfolded_lets n) :=
begin
  econstructor; unfold some_unfolded_lets psigma.fst; symmetry; transitivity; symmetry;
  {
    foo -- unify_reify_rhs_to_let_in
  }

end
