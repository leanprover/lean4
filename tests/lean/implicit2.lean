Variable f {A : Type} (x y : A) : A
Check f 10 20
Check f 10
Check f::explicit
Variable g {A : Type} (x1 x2 : A) {B : Type} (y1 y2 : B) : B
Check g 10 20 true
Check let r : Real -> Real -> Real := g 10 20
      in r
Check g 10
Set pp::implicit true
Check let r : Real -> Real -> Real := g 10 20
      in r
