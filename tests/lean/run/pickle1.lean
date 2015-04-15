import data.countable
open countable decidable bool prod list nat option
variable l : list (nat × bool)
check pickle l
eval pickle [2, 1]
example : unpickle (list nat) (pickle [1, 1]) = some [1, 1] :=
rfl
