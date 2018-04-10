example : ∀ (p q : Prop), p → q → p :=
begin
  intros p p h1 h2,
  exact h2,
end

example : ∀ (p q : Prop), p → q → p :=
begin
  intros p p h1 h2,
  dedup,
  exact h2,
end
