import logic data.unit

structure point (A : Type) (B : Type) :=
mk :: (x : A) (y : B)

structure point2 (A : Type) (B : Type) extends point A B :=
make

print prefix point2
