open nat

structure point (A B : Type) :=
(x : A) (y : B)

structure foo extends p1 : point nat nat, p2 : point bool bool renaming x→a y→b :=
(H1 : point.x p2 = point.y p2) (H2 : point.x p1 + point.y p1 > 10)

example (s : foo) : foo.a s = foo.b s :=
foo.H1 s

example (s : foo) : foo.x s + foo.y s > 10 :=
foo.H2 s
