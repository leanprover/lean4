parameter A : Type.{1}
parameters a b c : A
parameter f : A → A → A
check f a b
section
  parameters A B : Type
  parameters {C D : Type}
  parameters [e d : A]
  check A
  check B
  definition g (a : A) (b : B) (c : C) : A := e
end
check g.{2 1}
variables x y : A
