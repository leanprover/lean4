inductive term
| var : string → term
| app : string → list term → term

example (h : term.var "a" = term.app "f" []) : false :=
begin
  simp at h,
  exact false.elim h
end

example : ¬ term.var "a" = term.app "f" [] :=
by simp
