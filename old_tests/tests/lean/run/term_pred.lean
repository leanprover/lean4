inductive term
| app : string → list term → term
| var : string → term

inductive bin_only : term → Prop
| leaf    : ∀ x, bin_only (term.var x)
| bin_app : ∀ op a b, bin_only a → bin_only b → bin_only (term.app op [a, b])

example (op : string) (a : term) : ¬ bin_only (term.app op [a]) :=
begin
  intro h,
  cases h
end

example (op : string) (a b : term) (H : bin_only (term.app op [a, b])) : bin_only a :=
begin
  cases H,
  assumption
end

example (op : string) (a b : term) (H : bin_only (term.app op [a, b])) : bin_only b :=
begin
  cases H with _ _ _ _ H1 H2,
  exact H2
end
