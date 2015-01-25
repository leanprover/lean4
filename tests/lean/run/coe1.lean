prelude

constant A : Type.{1}
constant B : Type.{1}
constant f : A → B
attribute f [coercion]
constant g : B → B → B
constants a1 a2 a3 : A
constants b1 b2 b3 : B
check g a1 b1
set_option pp.coercions true
check g a1 b1

constant eq {A : Type} : A → A → Type.{0}
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
