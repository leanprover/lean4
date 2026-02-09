class NonUnitalNonAssocSemiring (α : Type u)

class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α

class Semiring (α : Type u) extends NonUnitalSemiring α

class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α

class CommSemiring (R : Type u) extends Semiring R

class NonUnitalNonAssocRing (α : Type u) extends NonUnitalNonAssocSemiring α

class NonUnitalRing (α : Type _) extends NonUnitalNonAssocRing α, NonUnitalSemiring α

class Ring (R : Type u) extends Semiring R

class NonUnitalCommRing (α : Type u) extends NonUnitalRing α

class CommRing (α : Type u) extends Ring α

instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }

instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }

instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [s : CommSemiring α] :
    NonUnitalCommSemiring α :=
  { s with }

instance (priority := 100) CommRing.toNonUnitalCommRing [s : CommRing α] : NonUnitalCommRing α :=
  { s with }

class StarRing' (R : Type _) [NonUnitalSemiring R]
def starGizmo [CommSemiring R] [StarRing' R] : R → R := id
theorem starGizmo_foo [CommRing R] [StarRing' R] (x : R) : starGizmo x = x := rfl

namespace ReidMWE

class A (α : Type u)

class B (α : Type u) extends A α

class C (α : Type u) extends B α

class D (α : Type u) extends B α

class E (α : Type u) extends C α, D α

class F (α : Type u) extends A α

class G (α : Type u) extends F α, B α

class H (α : Type u) extends C α

class I (α : Type u) extends G α, D α

class J (α : Type u) extends H α, I α, E α

class StarRing' (R : Type 0) [B R]
def starGizmo [E R] [StarRing' R] : R → R := id

theorem starGizmo_foo [J R] [StarRing' R] (x : R) : starGizmo x = x := rfl

theorem T (i : J R) : (@D.toB.{0} R (@E.toD.{0} R (@J.toE.{0} R i))) = i.toB := rfl
