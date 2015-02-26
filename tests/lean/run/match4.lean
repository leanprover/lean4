open nat bool inhabited prod

definition diag (a b c : bool) : nat :=
match (a, b, c) with
  | (_,  tt, ff) := 1
  | (ff, _,  tt) := 2
  | (tt, ff, _)  := 3
  | (_,  _,  _)  := arbitrary nat
end

theorem diag1 (a : bool) : diag a tt ff = 1 :=
bool.cases_on a rfl rfl

theorem diag2 (a : bool) : diag ff a tt = 2 :=
bool.cases_on a rfl rfl

theorem diag3 (a : bool) : diag tt ff a = 3 :=
bool.cases_on a rfl rfl

theorem diag4_1 : diag ff ff ff = arbitrary nat :=
rfl

theorem diag4_2 : diag tt tt tt = arbitrary nat :=
rfl
