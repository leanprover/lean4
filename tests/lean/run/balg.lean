import Lean

universe u

structure Magma where
  α   : Type u
  mul : α → α → α

instance : CoeSort Magma (Type u) where
  coe s := s.α

abbrev mul {M : Magma} (a b : M) : M :=
  M.mul a b

set_option pp.all true

infixl:70 (priority := high) "*" => mul

structure Semigroup extends Magma where
  mul_assoc (a b c : α) : a * b * c = a * (b * c)

instance : CoeSort Semigroup (Type u) where
  coe s := s.α

structure CommSemigroup extends Semigroup where
  mul_comm (a b : α) : a * b = b * a

structure Monoid extends Semigroup where
  one : α
  one_mul (a : α) : one * a = a
  mul_one (a : α) : a * one = a

instance : CoeSort Monoid (Type u) where
  coe s := s.α

structure CommMonoid extends Monoid where
  mul_comm (a b : α) : a * b = b * a

instance : Coe CommMonoid CommSemigroup where
  coe s := {
      α   := s.α
      mul := s.mul
      mul_assoc := s.mul_assoc
      mul_comm  := s.mul_comm
    }

structure Group extends Monoid where
  inv : α → α
  mul_left_inv (a : α) : (inv a) * a = one

instance : CoeSort Group (Type u) where
  coe s := s.α

abbrev inv {G : Group} (a : G) : G :=
  G.inv a

postfix:max "⁻¹" => inv

instance (G : Group) : OfNat (coeSort G.toMagma) (nat_lit 1) where
  ofNat := G.one

instance (G : Group) : OfNat (G.toMagma.α) (nat_lit 1) where
  ofNat := G.one

structure CommGroup extends Group where
  mul_comm (a b : α) : a * b = b * a

instance : CoeSort CommGroup (Type u) where
  coe s := s.α

theorem inv_mul_cancel_left {G : Group} (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← G.mul_assoc, G.mul_left_inv, G.one_mul]

theorem toMonoidOneEq {G : Group} : G.toMonoid.one = 1 :=
  rfl

theorem inv_eq_of_mul_eq_one {G : Group} {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  rw [← G.mul_one a⁻¹, toMonoidOneEq, ←h, ← G.mul_assoc, G.mul_left_inv, G.one_mul]

theorem inv_inv {G : Group} (a : G) : (a⁻¹)⁻¹ = a :=
  inv_eq_of_mul_eq_one (G.mul_left_inv a)

theorem mul_right_inv {G : Group} (a : G) : a * a⁻¹ = 1 := by
  have : a⁻¹⁻¹ * a⁻¹ = 1 := by rw [G.mul_left_inv]; rfl
  rw [inv_inv] at this
  assumption

unif_hint (G : Group) where
  |- G.toMonoid.one =?= 1

theorem mul_inv_rev {G : Group} (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply inv_eq_of_mul_eq_one
  rw [G.mul_assoc, ← G.mul_assoc b, mul_right_inv, G.one_mul, mul_right_inv]

theorem mul_inv {G : CommGroup} (a b : G) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [mul_inv_rev, G.mul_comm]
