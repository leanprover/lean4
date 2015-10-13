import data.num

namespace play
constants int nat real : Type.{1}
constant nat_add  : nat → nat → nat
constant int_add  : int → int → int
constant real_add : real → real → real

inductive add_struct [class] (A : Type) :=
mk : (A → A → A) → add_struct A

definition add {A : Type} {S : add_struct A} (a b : A) : A :=
add_struct.rec (λ m, m) S a b

infixl `+` := add

definition add_nat_struct  [instance] : add_struct nat := add_struct.mk nat_add
definition add_int_struct  [instance] : add_struct int := add_struct.mk int_add
definition add_real_struct [instance] : add_struct real := add_struct.mk real_add

constants n m : nat
constants i j : int
constants x y : real
constant num_to_nat : num → nat
constant nat_to_int : nat → int
constant int_to_real : int → real
attribute num_to_nat [coercion]
attribute nat_to_int [coercion]
attribute int_to_real [coercion]

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
namespace foo
constant eq {A : Type} : A → A → Prop
infixl `=` := eq
definition id (A : Type) (a : A) := a
notation A `=` B `:` C := @eq C A B
check nat_to_int n + nat_to_int m = (n + m) : int
end foo
end play
