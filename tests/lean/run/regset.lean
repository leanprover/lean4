namespace regset

section
parameter symbol : Type

@[reducible] def lang : Type :=
set (list symbol)

def concat : lang → lang → lang :=
λ a b : lang, { ll : list symbol | ∃xs ys : list symbol, ll = list.append xs ys ∧ xs ∈ a ∧ ys ∈ b }

end
end regset
