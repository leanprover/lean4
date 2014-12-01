prelude precedence `+` : 65
precedence `*` : 75
constant N : Type.{1}
check λ (f : N -> N -> N) (g : N → N → N) (infix + := f) (infix * := g) (x y : N), x+x*y
constant f : N → N → N
constant a : N
check a+a -- + notation is not available anymore
