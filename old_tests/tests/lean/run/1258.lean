constant P : list ℕ → list ℕ → Prop
lemma foo (xs : list ℕ) : Π (ns : list ℕ), P xs ns
| []      := sorry
| (n::ns) := begin clear foo, cases xs, exact sorry, exact sorry end
