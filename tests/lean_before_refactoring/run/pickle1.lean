import data.encodable
open encodable decidable bool prod list nat option
variable l : list (nat × bool)
check encode l
eval encode [2, 1]
example : decode (list nat) (encode [(1:nat), 1]) = some [1, 1] :=
rfl
