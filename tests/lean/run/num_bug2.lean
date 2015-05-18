import algebra.ring data.num
open algebra

variable A : Type
variable s : ring A
variable H0 : 0 = (0:A) -- since algebra defines notation '0' it should have precedence over num
variable H1 : 1 = (1:A) -- since algebra defines notation '1' it should have precedence over num

example : has_zero.zero A = has_zero.zero A :=
H0

example : has_one.one A = has_one.one A :=
H1
