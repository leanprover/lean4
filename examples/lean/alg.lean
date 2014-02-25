import macros

definition associative {A : (Type U)} (f : A → A → A)          := ∀ x y z, f (f x y) z = f x (f y z)
definition commutative {A : (Type U)} (f : A → A → A)          := ∀ x y, f x y = f y x
definition is_identity {A : (Type U)} (f : A → A → A) (id : A) := ∀ x, f x id = x
definition inverse_ex {A : (Type U)} (f : A → A → A) (id : A)  := ∀ x, ∃ y, f x y = id

definition struct := Type
definition carrier (s : struct) := s

definition mul_struct
:= sig s : struct, carrier s → carrier s → carrier s

definition mul_to_s (m : mul_struct) : struct := proj1 m
coercion mul_to_s

definition mul {m : mul_struct} : carrier m → carrier m → carrier m
:= proj2 m

infixl 70 * : mul

definition semi_group
:= sig m : mul_struct, associative (@mul m)

definition sg_to_mul (sg : semi_group) : mul_struct  := proj1 sg
definition sg_to_s (sg : semi_group) : struct        := mul_to_s (sg_to_mul sg)
coercion sg_to_s
coercion sg_to_mul

theorem sg_assoc {m : semi_group} (x y z : carrier m) : (x * y) * z = x * (y * z)
:= proj2 m x y z

definition monoid
:= sig sg : semi_group, sig id : carrier sg, is_identity (@mul sg) id

definition monoid_to_sg (m : monoid) : semi_group  := proj1 m
definition monoid_to_mul (m : monoid) : mul_struct := sg_to_mul (monoid_to_sg m)
definition monoid_to_s (m : monoid) : struct       := mul_to_s (monoid_to_mul m)
coercion monoid_to_sg
coercion monoid_to_mul
coercion monoid_to_s

definition one {m : monoid} : carrier m
:= proj1 (proj2 m)
theorem monoid_id {m : monoid} (x : carrier m) : x * one = x
:= proj2 (proj2 m) x

definition group
:= sig m : monoid, inverse_ex (@mul m) (@one m)

definition group_to_monoid (g : group) : monoid  := proj1 g
definition group_to_sg (g : group) : semi_group  := monoid_to_sg (group_to_monoid g)
definition group_to_mul (g : group) : mul_struct := sg_to_mul (group_to_sg g)
definition group_to_s (g : group) : struct       := mul_to_s (group_to_mul g)
coercion group_to_monoid
coercion group_to_sg
coercion group_to_mul
coercion group_to_s

theorem group_inv {g : group} (x : carrier g) : ∃ y, x * y = one
:= proj2 g x

definition abelian_group
:= sig g : group, commutative (@mul g)

definition abelian_to_group  (ag : abelian_group) : group     := proj1 ag
definition abelian_to_monoid (ag : abelian_group) : monoid    := group_to_monoid (abelian_to_group ag)
definition abelian_to_sg (ag : abelian_group) : semi_group    := monoid_to_sg (abelian_to_monoid ag)
definition abelian_to_mul (ag : abelian_group) : mul_struct   := sg_to_mul (abelian_to_sg ag)
definition abelian_to_s (ag : abelian_group) : struct         := mul_to_s (abelian_to_mul ag)
coercion abelian_to_group
coercion abelian_to_monoid
coercion abelian_to_sg
coercion abelian_to_mul
coercion abelian_to_s

theorem abelian_comm {ag : abelian_group} (x y : carrier ag) : x * y = y * x
:= proj2 ag x y

theorem abelian_left_comm {ag : abelian_group} (x y z : carrier ag) : x * (y * z) = y * (x * z)
:= calc x * (y * z) = (x * y) * z    : symm (sg_assoc x y z)
              ...   = (y * x) * z    : { abelian_comm x y }
              ...   = y * (x * z)    : sg_assoc y x z
