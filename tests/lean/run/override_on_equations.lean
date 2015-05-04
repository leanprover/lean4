open nat

inductive expr :=
| zero : expr
| one  : expr
| add  : expr → expr → expr

namespace expr

infix `+` := expr.add

set_option pp.notation false

definition ev : expr → nat
| zero          := 0
| one           := 1
| #expr (a + b) := ev a + ev b

definition foo : expr := add zero (add one one)

example : ev foo = 2 :=
rfl

end expr
