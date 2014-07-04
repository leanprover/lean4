variable N : Type.{1}
variable f : N → N → N → N
variable g : N → N → N
variable h : N → N → N → N
variable s : N → N → N → N → N

precedence `*`:75
precedence `|`:75

notation a * b:prev | c:prev := f a b c
notation a * b := g a b
notation a * b * c:prev := h a b c
notation a * b | c * d:prev := s a b c d

variables a b c d e : N

check a * b
check a * b | d
check a * b * c
check a * b | d * e
