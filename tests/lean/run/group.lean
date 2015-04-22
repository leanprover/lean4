import logic

section
  variable {A  : Type}
  variable f   : A → A → A
  variable one : A
  variable inv : A → A
  local infixl `*`   := f
  local postfix `^-1`:100 := inv
  definition is_assoc := ∀ a b c, (a*b)*c = a*b*c
  definition is_id    := ∀ a, a*one = a
  definition is_inv   := ∀ a, a*a^-1 = one
end

inductive group_struct [class] (A : Type) : Type :=
mk_group_struct : Π (mul : A → A → A) (one : A) (inv : A → A), is_assoc mul → is_id mul one → is_inv mul one inv → group_struct A

inductive group : Type :=
mk_group : Π (A : Type), group_struct A → group

definition carrier (g : group) : Type
:= group.rec (λ c s, c) g

definition group_to_struct [instance] (g : group) : group_struct (carrier g)
:= group.rec (λ (A : Type) (s : group_struct A), s) g

check group_struct

definition mul {A : Type} {s : group_struct A} (a b : A) : A
:= group_struct.rec (λ mul one inv h1 h2 h3, mul) s a b

infixl `*` := mul

constant  G1 : group.{1}
constant  G2 : group.{1}
constants a b c : (carrier G2)
constants d e : (carrier G1)
check a * b * b
check d * e
