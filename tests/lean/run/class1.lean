import logic data.prod data.num
open prod inhabited

definition H : inhabited (Prop × num × (num → num)) := _

(*
print(get_env():find("H"):value())
*)
