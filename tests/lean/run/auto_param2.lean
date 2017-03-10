open tactic

meta def my_tac : tactic unit :=
assumption <|> abstract (comp_val >> skip) <|> fail "my_tac failed to synthesize auto_param"

def f (x : nat) (h : x > 0 . my_tac) : nat :=
nat.pred x

#check f 12
#check f 13

lemma f_inj {x₁ x₂ : nat} {h₁ : x₁ > 0} {h₂ : x₂ > 0} : f x₁ = f x₂ → x₁ = x₂ :=
begin
  unfold f, intro h,
  cases x₁,
  exact absurd h₁ (lt_irrefl _),
  cases x₂,
  exact absurd h₂ (lt_irrefl _),
  apply congr_arg nat.succ,
  assumption
end

#check @f_inj

lemma f_def {x : nat} (h : x > 0) : f x = nat.pred x :=
rfl

-- The following is an error
-- #check λ x, f x
