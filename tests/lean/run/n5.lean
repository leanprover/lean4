prelude
constant N : Type.{1}
constant f : N → N → N → N
constant g : N → N → N
constant h : N → N → N → N
constant s : N → N → N → N → N

precedence `*`:75
precedence `|`:75

notation a * b:prev | c:prev := f a b c
notation a * b := g a b
notation a * b * c:prev := h a b c
notation a * b | c * d:prev := s a b c d

constants a b c d e : N

check a * b
check a * b | d
check a * b * c
check a * b | d * e
