import logic data.prod data.examples.vector
open prod nat inhabited vector

theorem tst1 : inhabited (vector nat 2)

theorem tst2 : inhabited (Prop × (Π n : nat, vector nat n))

reveal tst2
(*
print(get_env():find("tst2"):value())
*)
