precedence `+` : 65
precedence `*` : 75
variable N : Type.{1}
check λ (f : N -> N -> N) (g : N → N → N) (infix + := f) (infix * := g) (x y : N), x+x*y
variable f : N → N → N
variable a : N
check a+a -- + notation is not available anymore
