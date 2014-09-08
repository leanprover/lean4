import logic data.prod data.vector
open prod nat inhabited vec

theorem tst1 : inhabited (vec nat 2)

theorem tst2 : inhabited (Prop × (Π n : nat, vec nat n))

(*
print(get_env():find("tst2"):value())
*)
