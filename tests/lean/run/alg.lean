class Semigroup (α : Type u) extends Mul α where
  mul_assoc (a b c : α) : a * b * c = a * (b * c)

export Semigroup (mul_assoc)

class MulComm (α : Type u)  extends Mul α where
  mul_comm (a b : α) : a * b = b * a

export MulComm (mul_comm)

class CommSemigroup (α : Type u) extends Semigroup α where
  mul_comm (a b : α) : a * b = b * a

instance [CommSemigroup α] : MulComm α where
  mul_comm := CommSemigroup.mul_comm

class Monoid (α : Type u) extends Semigroup α, One α where
  one_mul (a : α) : 1 * a = a
  mul_one (a : α) : a * 1 = a

export Monoid (one_mul mul_one)

class CommMonoid (α : Type u) extends Monoid α where
  mul_comm (a b : α) : a * b = b * a

instance [CommMonoid α] : CommSemigroup α where
  mul_comm := CommMonoid.mul_comm

instance [CommMonoid α] : MulComm α where
  mul_comm := CommSemigroup.mul_comm

class Inv (α : Type u) where
  inv : α → α

postfix:max "⁻¹" => Inv.inv

class Group (α : Type u) extends Monoid α, Inv α where
  mul_left_inv (a : α) : a⁻¹ * a = 1

export Group (mul_left_inv)

class CommGroup (α : Type u) extends Group α where
  mul_comm (a b : α) : a * b = b * a

instance [CommGroup α] : CommMonoid α where
  mul_comm := CommGroup.mul_comm

instance [CommGroup α] : MulComm α where
  mul_comm := CommGroup.mul_comm

theorem inv_mul_cancel_left [Group α] (a b : α) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, mul_left_inv, one_mul]

theorem inv_eq_of_mul_eq_one [Group α] {a b : α} (h : a * b = 1) : a⁻¹ = b := by
  rw [← mul_one a⁻¹, ←h, ←mul_assoc, mul_left_inv, one_mul]

theorem inv_inv [Group α] (a : α) : (a⁻¹)⁻¹ = a :=
  inv_eq_of_mul_eq_one (mul_left_inv a)

theorem mul_right_inv [Group α] (a : α) : a * a⁻¹ = 1 := by
  have : a⁻¹⁻¹ * a⁻¹ = 1 := by rw [mul_left_inv]
  rw [inv_inv] at this
  assumption

theorem mul_inv_rev [Group α] (a b : α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply inv_eq_of_mul_eq_one
  rw [mul_assoc, ← mul_assoc b, mul_right_inv, one_mul, mul_right_inv]

theorem mul_inv [CommGroup α] (a b : α) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [mul_inv_rev, mul_comm]
