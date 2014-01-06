variable N : Type
variable f : Bool -> Bool -> Bool
variable g : N -> N -> N
infixl 10 ++ : f
infixl 10 ++ : g
print true ++ false ++ true
set::option lean::pp::notation false
print true ++ false ++ true
variable a : N
variable b : N
print a ++ b ++ a
print true ++ false ++ false