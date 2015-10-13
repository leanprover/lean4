set_option structure.eta_thm true
set_option structure.proj_mk_thm true

structure semigroup [class] (A : Type) extends has_mul A :=
(mul_assoc : ∀a b c, mul (mul a b) c = mul a (mul b c))

structure comm_semigroup [class] (A : Type) extends semigroup A :=
(mul_comm : ∀a b, mul a b = mul b a)

structure left_cancel_semigroup [class] (A : Type) extends semigroup A :=
(mul_left_cancel : ∀a b c, mul a b = mul a c → b = c)

structure right_cancel_semigroup [class] (A : Type) extends semigroup A :=
(mul_right_cancel : ∀a b c, mul a b = mul c b → a = c)

structure add_semigroup [class] (A : Type) extends has_add A :=
(add_assoc : ∀a b c, add (add a b) c = add a (add b c))

structure add_comm_semigroup [class] (A : Type) extends add_semigroup A :=
(add_comm : ∀a b, add a b = add b a)

structure add_left_cancel_semigroup [class] (A : Type) extends add_semigroup A :=
(add_left_cancel : ∀a b c, add a b = add a c → b = c)

structure add_right_cancel_semigroup [class] (A : Type) extends add_semigroup A :=
(add_right_cancel : ∀a b c, add a b = add c b → a = c)

structure monoid [class] (A : Type) extends semigroup A, has_one A :=
(one_mul : ∀a, mul one a = a) (mul_one : ∀a, mul a one = a)

structure comm_monoid [class] (A : Type) extends monoid A, comm_semigroup A

structure add_monoid [class] (A : Type) extends add_semigroup A, has_zero A :=
(zero_add : ∀a, add zero a = a) (add_zero : ∀a, add a zero = a)

structure add_comm_monoid [class] (A : Type) extends add_monoid A, add_comm_semigroup A

structure group [class] (A : Type) extends monoid A, has_inv A :=
(mul_left_inv : ∀a, mul (inv a) a = one)

structure comm_group [class] (A : Type) extends group A, comm_monoid A

structure add_group [class] (A : Type) extends add_monoid A, has_neg A :=
(add_left_inv : ∀a, add (neg a) a = zero)

structure add_comm_group [class] (A : Type) extends add_group A, add_comm_monoid A

structure distrib [class] (A : Type) extends has_mul A, has_add A :=
(left_distrib : ∀a b c, mul a (add b c) = add (mul a b) (mul a c))
(right_distrib : ∀a b c, mul (add a b) c = add (mul a c) (mul b c))

structure mul_zero_class [class] (A : Type) extends has_mul A, has_zero A :=
(zero_mul : ∀a, mul zero a = zero)
(mul_zero : ∀a, mul a zero = zero)

structure zero_ne_one_class [class] (A : Type) extends has_zero A, has_one A :=
(zero_ne_one : zero ≠ one)

structure semiring [class] (A : Type) extends add_comm_monoid A, monoid A, distrib A,
    mul_zero_class A, zero_ne_one_class A

set_option pp.implicit true
check @semiring.mul.mk
check @semiring.eta
