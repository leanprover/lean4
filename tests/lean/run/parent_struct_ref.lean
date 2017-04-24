open nat

structure point (A B : Type) :=
(x : A) (y : B)

structure foo extends p1 : point nat nat :=
(H1 : point.x p1 + point.y p1 > 10)

#check foo.p1
#check foo.H1
