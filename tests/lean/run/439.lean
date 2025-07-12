set_option pp.mvars false

universe u

structure Fn (E I : Sort u) := (exp : E) (imp : I)
instance (E I : Sort u) :  CoeFun (Fn E I) (fun _ => I) := {coe := fun K => K.imp}

class Bar.{w} (P : Sort u) :=
  fn : P -> Sort w

variable {P : Sort u} (B : Bar P)
variable (fn : Fn ((p : P) -> B.fn p) ({p : P} -> B.fn p))
#check (@fn : {p : P} → Bar.fn p) -- Result is as expected (implicit)
/-
  fn.imp : {p : P} → Bar.fn p
-/

variable (p : P)
variable (Bp : Bar.fn p)
/--
error: Function expected at
  fn.imp
but this term has type
  Bar.fn ?_

Note: Expected a function because this term is being applied to the argument
  Bp
-/
#guard_msgs in
#check fn Bp

/--
error: Function expected at
  fn.imp
but this term has type
  Bar.fn ?_

Note: Expected a function because this term is being applied to the argument
  p
-/
#guard_msgs in
#check fn p

#check fn (p := p)

variable (fn' : Fn ((p : P) -> B.fn p -> B.fn p) ({p : P} -> B.fn p -> B.fn p))

#check fn' Bp

/--
error: Application type mismatch: The argument
  p
has type
  P
but is expected to have type
  Bar.fn ?_
in the application
  fn'.imp p
-/
#guard_msgs in
#check fn' p
