import logic data.prod
open prod inhabited

section
  variable {A : Type}
  variable {B : Type}
  variable Ha : inhabited A
  variable Hb : inhabited B
  include Ha Hb
  theorem tst : inhabited (Prop × A × B)

end

reveal tst
(*
print(get_env():find("tst"):value())
*)
