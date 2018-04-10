open nat bool inhabited

definition diag : bool → bool → bool → nat
| b  tt ff := 1
| ff b  tt := 2
| tt ff b  := 3
| b1 b2 b3 := arbitrary nat

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
