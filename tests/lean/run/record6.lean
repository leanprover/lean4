import logic data.unit

structure point (A : Type) (B : Type) :=
mk :: (x : A) (y : B)

structure point2 (A : Type) (B : Type) extends point A B :=
make

structure point3 extends point num num, private point2 num num renaming x→y y→z

check point3.mk

theorem tst : point3.mk 1 2 3 = point.mk 1 2 :=
rfl
