
structure A :=
(x y : Nat)

structure B :=
(z : Nat)

structure C extends A, B

def f (c : C) :=
c.x + c.y + c.z

theorem ex1 : f {x := 10, y := 20, z := 30} = 60 :=
rfl

structure D

def g (d : D) : D :=
d

theorem ex2 : g {} = {} :=
rfl

theorem ex3 (d : D) : g d = {} := by
 cases d
 exact rfl
