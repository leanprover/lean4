import standard
using num prod nonempty inhabited

theorem H {A B : Type} (H1 : inhabited A) : inhabited (Prop × A × (B → num))
:= _

(*
print(get_env():find("H"):value())
*)
