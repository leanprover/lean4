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
error: function expected at
  fn.imp
term has type
  Bar.fn ?_
-/
#guard_msgs in
#check fn Bp

/--
error: function expected at
  fn.imp
term has type
  Bar.fn ?_
-/
#guard_msgs in
#check fn p

#check fn (p := p)

variable (fn' : Fn ((p : P) -> B.fn p -> B.fn p) ({p : P} -> B.fn p -> B.fn p))

#check fn' Bp

/--
error: application type mismatch
  fn'.imp p
argument
  p
has type
  P : Sort u
but is expected to have type
  Bar.fn ?_ : Sort _
-/
#guard_msgs in
#check fn' p
