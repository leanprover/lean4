universe u
class Bar.{w} (P : Sort u) where
  fn : P -> Sort w

variable {P : Sort u} (B : Bar P)
structure Foo (X Y : Sort u) where f : Unit
def foo := Foo ((p : P) -> B.fn p) ({p : P} -> B.fn p)


#print foo
