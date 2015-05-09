import logic data.prod data.num
open prod nonempty inhabited

theorem H {A B : Type} (H1 : inhabited A) : inhabited (Prop × A × (B → num))
:= _
wait H
(*
print(get_env():find("H"):value())
*)
