constant α: Type

inductive P: α → Prop

inductive Q: α → α → Prop
| of: ∀ {a₁ a₂}, Q a₁ a₂

example {a: α} (P_a: P a) (Q_a: ∃ a', Q a' a): true :=
begin
  cases Q_a with a' Q_a'_a,
  cases Q_a'_a,
  cases P_a,
end
