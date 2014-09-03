import logic data.prod
open num prod inhabited

section
  parameter {A : Type}
  parameter {B : Type}
  parameter Ha : inhabited A
  parameter Hb : inhabited B
  -- The section mechanism only includes parameters that are explicitly cited.
  -- So, we use the 'including' expression to make explicit we want to use
  -- Ha and Hb
  theorem tst : inhabited (Prop × A × B)
  := including Ha Hb, _

end

(*
print(get_env():find("tst"):value())
*)
