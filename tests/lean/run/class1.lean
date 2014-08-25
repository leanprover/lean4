import logic data.prod
using num prod inhabited

definition H : inhabited (Prop × num × (num → num)) := _

(*
print(get_env():find("H"):value())
*)
