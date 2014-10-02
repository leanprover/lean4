constant A : Type.{1}
constants a b c : A
constant f : A → A → A
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
constants x y : A
