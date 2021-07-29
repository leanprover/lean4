set_option pp.analyze.trustCoe true

universe u

structure Fn (E I : Sort u) := (exp : E) (imp : I)
instance (E I : Sort u) :  CoeFun (Fn E I) (fun _ => I) := {coe := fun K => K.imp}

class Bar.{w} (P : Sort u) :=
  fn : P -> Sort w

variable {P : Sort u} (B : Bar P)
variable (fn : Fn ((p : P) -> B.fn p) ({p : P} -> B.fn p))
#check coeFun fn -- Result is as expected (implicit)
/-
  fn : {p : P} → Bar.fn p
-/

variable (p : P)
variable (Bp : Bar.fn p)
#check fn Bp
/-
application type mismatch
  Fn.imp fn Bp
argument
  Bp
has type
  Bar.fn p : Sort ?u.635
but is expected to have type
  P : Sort u
-/
#check fn p
#check fn (p := p)


variable (fn' : Fn ((p : P) -> B.fn p -> B.fn p) ({p : P} -> B.fn p -> B.fn p))

-- Expect no error
#check fn' Bp

-- Expect error
#check fn' p
