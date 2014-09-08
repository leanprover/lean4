import data.num


variables int nat real : Type.{1}
variable nat_add  : nat → nat → nat
variable int_add  : int → int → int
variable real_add : real → real → real

inductive add_struct (A : Type) :=
mk : (A → A → A) → add_struct A

definition add {A : Type} {S : add_struct A} (a b : A) : A :=
add_struct.rec (λ m, m) S a b

infixl `+`:65 := add

definition add_nat_struct  [instance] : add_struct nat := add_struct.mk nat_add
definition add_int_struct  [instance] : add_struct int := add_struct.mk int_add
definition add_real_struct [instance] : add_struct real := add_struct.mk real_add

variables n m : nat
variables i j : int
variables x y : real
variable num_to_nat : num → nat
variable nat_to_int : nat → int
variable int_to_real : int → real
coercion num_to_nat
coercion nat_to_int
coercion int_to_real

set_option pp.implicit true
set_option pp.coercions true
check n + m
check i + j
check x + y
check i + n
check i + x
check n + i
check x + i
check n + x
check x + n
check x + i + n
check n + 0
check 0 + n
check 0 + i
check i + 0
check 0 + x
check x + 0
namespace foo
variable eq {A : Type} : A → A → Prop
infixl `=`:50 := eq
abbreviation id (A : Type) (a : A) := a
notation A `=` B `:` C := @eq C A B
check nat_to_int n + nat_to_int m = (n + m) : int
end foo
