import standard
using num pair

theorem H {A B : Type} (H1 : inhabited A) : inhabited (Bool × A × (B → num))
:= _

(*
print(get_env():find("H"):value())
*)