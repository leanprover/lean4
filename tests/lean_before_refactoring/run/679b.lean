import data.finset
open bool nat list finset

attribute [class]
definition fset (A : Type) := finset A

attribute [instance]
definition fin_nat : fset nat :=
to_finset [0]

attribute [instance]
definition fin_bool : fset bool :=
to_finset [tt, ff]

definition tst (A : Type) [s : fset A] : finset A :=
s

example : tst nat = to_finset [0] :=
rfl

example : tst bool = to_finset [ff, tt] :=
dec_trivial

example : tst bool = to_finset [tt, ff] :=
rfl
