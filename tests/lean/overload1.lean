Variable N : Type
Variable f : Bool -> Bool -> Bool
Variable g : N -> N -> N
Infixl 10 ++ : f
Infixl 10 ++ : g
print true ++ false ++ true
SetOption lean::pp::notation false
print true ++ false ++ true
Variable a : N
Variable b : N
print a ++ b ++ a
print true ++ false ++ false