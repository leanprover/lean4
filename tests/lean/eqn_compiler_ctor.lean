import data.stream

inductive term
| var : ℕ → term
| app : term → term → term
| abs : term → term

open term

def subst : ∀ σ : ℕ → term, term → term
| var := sorry
