import standard
using num

section
  parameter {A  : Type}
  parameter f   : A → A → A
  parameter one : A
  parameter inv : A → A
  infixl `*`:75     := f
  postfix `^-1`:100 := inv
  definition is_assoc := ∀ a b c, (a*b)*c = a*b*c
  definition is_id    := ∀ a, a*one = a
  definition is_inv   := ∀ a, a*a^-1 = one
end

inductive group_struct (A : Type) : Type :=
| mk_group_struct : Π (mul : A → A → A) (one : A) (inv : A → A), is_assoc mul → is_id mul one → is_inv mul one inv → group_struct A

class group_struct

inductive group : Type :=
| mk_group : Π (A : Type), group_struct A → group

definition carrier (g : group) : Type
:= group_rec (λ c s, c) g

coercion carrier

definition group_to_struct [instance] (g : group) : group_struct (carrier g)
:= group_rec (λ (A : Type) (s : group_struct A), s) g

check group_struct

definition mul [inline] {A : Type} {s : group_struct A} (a b : A) : A
:= group_struct_rec (λ mul one inv h1 h2 h3, mul) s a b

infixl `*`:75 := mul

section
  variable  G1 : group
  variable  G2 : group
  variables a b c : G2
  variables d e   : G1
  check a * b * b
  check d * e
end

variable G : group.{1}
variables a b : G
definition val : G := a*b
check val

variable pos_real : Type.{1}
variable rmul  : pos_real → pos_real → pos_real
variable rone  : pos_real
variable rinv  : pos_real → pos_real
axiom    H1    : is_assoc rmul
axiom    H2    : is_id rmul rone
axiom    H3    : is_inv rmul rone rinv

definition real_group_struct [inline] [instance] : group_struct pos_real
:= mk_group_struct rmul rone rinv H1 H2 H3

variables x y : pos_real
check x * y
theorem T (a b : pos_real): (rmul a b) = a*b
:= refl (rmul a b)
