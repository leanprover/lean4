open nat

inductive Expr :=
| zero : Expr
| one  : Expr
| add  : Expr → Expr → Expr

namespace Expr

infix `+` := Expr.add

set_option pp.notation false

definition ev : Expr → nat
| zero          := 0
| one           := 1
| #Expr (a + b) := ev a + ev b

definition foo : Expr := add zero (add one one)

example : ev foo = 2 :=
rfl

end Expr
