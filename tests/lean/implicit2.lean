import Real.
variable f {A : Type} (x y : A) : A
check f 10 20
check f 10
check @f
variable g {A : Type} (x1 x2 : A) {B : Type} (y1 y2 : B) : B
check g 10 20 true
check let r : Real -> Real -> Real := g 10 20
      in r
check g 10
setoption pp::implicit true
check let r : Real -> Real -> Real := g 10 20
      in r
