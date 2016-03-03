import data.int
open nat int

variable f : int → int
variable a : nat

constant bv : nat → Type₁
attribute bv [coercion]
constant g : Π {n : nat}, bv n → bv n

set_option pp.all true

check f a
check fun x : a, g x


set_option elaborator.coercions false

check f a            -- ERROR
check fun x : a, g x -- ERROR
