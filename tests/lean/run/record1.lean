import logic data.unit


structure point (A : Type) (B : Type) :=
mk :: (x : A) (y : B)

check point
check @ point.rec
check point.mk
check point.x
check point.y
check point.rec_on
check point.induction_on
check point.destruct

inductive color :=
red | green | blue

structure color_point (A : Type) (B : Type) extends point A B :=
mk :: (c : color)

check @color_point.rec_on
check color_point.rec_on
check color_point.to_point

section
variables a b : num

example : point.x (point.mk a b) = a :=
rfl

example : point.y (point.mk a b) = b :=
rfl

variables cc : color

example : color_point.x (color_point.mk a b cc) = a :=
rfl

example : color_point.y (color_point.mk a b cc) = b :=
rfl

example : color_point.c (color_point.mk a b cc) = cc :=
rfl

example : color_point.to_point (color_point.mk a b cc) = point.mk a b :=
rfl
end
