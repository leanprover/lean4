structure pointed [class] (A : Type) := (point : A)

open unit pointed

definition pointed_unit [instance] [constructor] : pointed unit :=
mk star

example : point unit = point unit := by esimp
