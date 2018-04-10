structure point (A : Type) (B : Type) :=
mk :: (x : A) (y : B)

inductive color
| red | green | blue

structure color_point (A : Type) (B : Type) extends point A B :=
mk :: (c : color)
