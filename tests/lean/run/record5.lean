import logic data.unit

structure point (A : Type) (B : Type) :=
mk :: (x : A) (y : B)

structure point2 (A : Type) (B : Type) extends point A B :=
make

check point2.make

structure point3 extends point num num, point2 num num renaming x→y y→z

check point3.mk

set_option pp.coercions true

theorem tst : point3.mk 1 2 3 = point2.make 2 3 :=
rfl
