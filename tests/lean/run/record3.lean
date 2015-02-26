import logic data.unit


structure point (A : Type) (B : Type) :=
mk :: (x : A) (y : B)

inductive color :=
red | green | blue

structure color_point (A : Type) (B : Type) extends point A B :=
mk :: (c : color)

constant foo (p: point num num) : num

constant p : color_point num num
set_option pp.coercions true
check foo p
