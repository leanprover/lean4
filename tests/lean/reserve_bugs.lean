import logic

constant f : num → num
constant g : num → num → num
constant h : num → num → num

reserve infixl `+`:65
reserve infixr `&`:70
reserve infixl `-`:65
reserve prefix `-`:100


infixl `+` := g
infixl `-` := h
prefix `-` := f
infixr `&` := h

set_option pp.notation false

check -(1:num) + 2
check 1 & 2 & 3 & 4
check (1:num) - 2 - 3 - 4

infixr `~~`:60 := h
infixl `!!`:60 := h

check 1 ~~ 2 ~~ 3 ~~ 4
check 1 !! 2 !! 3 !! 4
check 1 ~~ 2 + 3 ~~ 4
