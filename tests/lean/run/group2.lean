import logic

context
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
mk : Π (mul : A → A → A) (one : A) (inv : A → A), is_assoc mul → is_id mul one → is_inv mul one inv → group_struct A

inductive group : Type :=
mk : Π (A : Type), group_struct A → group

definition carrier (g : group) : Type
:= group.rec (λ c s, c) g

coercion carrier

definition group_to_struct [instance] (g : group) : group_struct (carrier g)
:= group.rec (λ (A : Type) (s : group_struct A), s) g

check group_struct

definition mul {A : Type} {s : group_struct A} (a b : A) : A
:= group_struct.rec (λ mul one inv h1 h2 h3, mul) s a b

infixl `*`:75 := mul

section
  parameter  G1 : group
  parameter  G2 : group
  parameters a b c : G2
  parameters d e   : G1
  check a * b * b
  check d * e
end

constant G : group.{1}
constants a b : G
definition val : G := a*b
check val

constant pos_real : Type.{1}
constant rmul  : pos_real → pos_real → pos_real
constant rone  : pos_real
constant rinv  : pos_real → pos_real
axiom    H1    : is_assoc rmul
axiom    H2    : is_id rmul rone
axiom    H3    : is_inv rmul rone rinv

definition real_group_struct [instance] : group_struct pos_real
:= group_struct.mk rmul rone rinv H1 H2 H3

constants x y : pos_real
check x * y
set_option pp.implicit true
print "---------------"
theorem T (a b : pos_real): (rmul a b) = a*b
:= eq.refl (rmul a b)
