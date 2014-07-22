import standard
using num pair

theorem H {A B : Type} (H1 : inhabited A) : inhabited (Prop × A × (B → num))
:= _

(*
print(get_env():find("H"):value())
*)