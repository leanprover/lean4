opaque a b : Nat

opaque a b c : Nat

opaque a b c d : Nat

opaque a b c d e: Nat

opaque a b (c : _) : Nat

opaque a α β : β → Bool
set_option pp.rawOnError true

example x : True := sorry

example x y : True := sorry

example x y z : True := sorry

example α β γ : β → True := sorry

example x y (c : True) : True := sorry
