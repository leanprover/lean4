--

constant f : nat → nat
constant g : nat → nat → nat
constant h : nat → nat → nat

reserve infixl `+`:65
reserve infixr `&`:70
reserve infixl `-`:65
reserve prefix `-`:100


local infixl `+` := g
local infixl `-` := h
local prefix `-` := f
local infixr `&` := h

set_option pp.notation false

#check -(1:nat) + 2
#check 1 & 2 & 3 & 4
#check (1:nat) - 2 - 3 - 4

infixr `~~`:60 := h
infixl `!!`:60 := h

#check 1 ~~ 2 ~~ 3 ~~ 4
#check 1 !! 2 !! 3 !! 4
#check 1 ~~ 2 + 3 ~~ 4
