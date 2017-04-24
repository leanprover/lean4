structure point (A : Type) (B : Type) :=
mk :: (x : A) (y : B)

#check point
#check @ point.rec
#check point.mk
#check point.x
#check point.y
#check point.rec_on

inductive color
| red | green | blue

structure color_point (A : Type) (B : Type) extends point A B :=
mk :: (c : color)

#check @color_point.rec_on
#check color_point.rec_on
#check color_point.to_point

section
variables a b : num

example : point.x (point.mk a b) = a :=
rfl

example : point.y (point.mk a b) = b :=
rfl

variables cc : color

example : {color_point . x := a, y := b, c := cc}.x = a :=
rfl

example : {color_point . x := a, y := b, c := cc}.y = b :=
rfl

example : {color_point . x := a, y := b, c := cc}.c = cc :=
rfl

example : {color_point . x := a, y := b, c := cc}.to_point = point.mk a b :=
rfl
end
