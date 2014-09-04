variable A : Type.{1}
variable B : Type.{1}
variable f : A → B
coercion f
variable g : B → B → B
variables a1 a2 a3 : A
variables b1 b2 b3 : B
check g a1 b1
set_option pp.coercion true
check g a1 b1

variable eq {A : Type} : A → A → Type.{0}
check eq a1 a2
check eq a1 b1
set_option pp.implicit true
check eq a1 b1
set_option pp.universes true
check eq a1 b1

inductive pair (A : Type) (B: Type) : Type :=
mk : A → B → pair A B

check pair.mk a1 b2
check B
check pair.mk
set_option pp.unicode false
check pair.mk
set_option pp.implicit false
check pair.mk
check pair
