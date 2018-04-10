open tactic

example (p q : Prop) [s₁ : decidable p] [s₂ : decidable q] : true :=
begin
  unfreeze_local_instances,
  with_cases { cases s₁; cases s₂ },
  trace_state,
  all_goals { intros, trivial }
end

def split (p : Prop) {q : Prop} [decidable p] (pos : p → q) (neg : ¬ p → q) : q :=
decidable.by_cases pos neg

example (p q : Prop) [decidable p] [decidable q] : true :=
begin
  with_cases { apply split p; apply split q; intros hq hp },
  trace_state,
  all_goals { intros, trivial }
end
