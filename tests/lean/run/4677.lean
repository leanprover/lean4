inductive Bob where | mk (x : Int)
deriving Repr

/--
info: Bob.mk (-1)
-/
#guard_msgs in
#eval Bob.mk (-1)

/--
info: [-1, 2]
-/
#guard_msgs in
#eval [(3 : Int) - 4, 2]

/--
info: -2
-/
#guard_msgs in
#eval -3 + 1

/--
info: Bob.mk 2
-/
#guard_msgs in
#eval Bob.mk 2

inductive Boo where | mk (x : Float)
deriving Repr

/--
info: [-1.000000, 2.000000]
-/
#guard_msgs in
#eval [-1.0, 2.0]

/--
info: Boo.mk (-1.000000)
-/
#guard_msgs in
#eval Boo.mk (-1.0)

/--
info: Boo.mk 1.000000
-/
#guard_msgs in
#eval Boo.mk 1.0

/--
info: -1.000000
-/
#guard_msgs in
#eval -1.0
