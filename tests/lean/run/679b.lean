import data.finset
open bool nat list finset

definition fset [class] (A : Type) := finset A

definition fin_nat [instance] : fset nat :=
to_finset [0]

definition fin_bool [instance] : fset bool :=
to_finset [tt, ff]

definition tst (A : Type) [s : fset A] : finset A :=
s

example : tst nat = to_finset [0] :=
rfl

example : tst bool = to_finset [ff, tt] :=
dec_trivial

example : tst bool = to_finset [tt, ff] :=
rfl
