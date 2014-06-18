variable A : Type.{1}
variable a : A
variable g : A → A
variable f : A → A → A

(*
function foo()
  return Const("g")(parse_expr())
end
*)

notation `tst` c1:(call foo) `with` c2:(call foo) := f c1 c2
notation `simple` c:(call foo) := c
variable b : A
check tst (simple b) with a
