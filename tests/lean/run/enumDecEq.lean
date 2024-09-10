inductive Foo1 where
  | a1
  deriving DecidableEq

/--
info: def Foo1.ofNat : Nat → Foo1 :=
fun n => Foo1.a1
-/
#guard_msgs in
#print Foo1.ofNat

inductive Foo2 where
  | a1 | a2
  deriving DecidableEq

/--
info: def Foo2.ofNat : Nat → Foo2 :=
fun n => bif n.beq 0 then Foo2.a1 else Foo2.a2
-/
#guard_msgs in
#print Foo2.ofNat

inductive Foo3 where
  | a1 | a2 | a3
  deriving DecidableEq

/--
info: def Foo3.ofNat : Nat → Foo3 :=
fun n => bif Nat.ble 1 n then bif n.beq 1 then Foo3.a2 else Foo3.a3 else Foo3.a1
-/
#guard_msgs in
#print Foo3.ofNat

inductive Foo4 where
  | a1 | a2 | a3 | a4
  deriving DecidableEq

/--
info: def Foo4.ofNat : Nat → Foo4 :=
fun n => bif Nat.ble 2 n then bif n.beq 2 then Foo4.a3 else Foo4.a4 else bif n.beq 0 then Foo4.a1 else Foo4.a2
-/
#guard_msgs in
#print Foo4.ofNat

inductive Foo5 where
  | a1 | a2 | a3 | a4 | a5
  deriving DecidableEq

/--
info: def Foo5.ofNat : Nat → Foo5 :=
fun n =>
  bif Nat.ble 2 n then bif Nat.ble 3 n then bif n.beq 3 then Foo5.a4 else Foo5.a5 else Foo5.a3
  else bif n.beq 0 then Foo5.a1 else Foo5.a2
-/
#guard_msgs in
#print Foo5.ofNat
