Variable N : Type
Variable f : Bool -> Bool -> Bool
Variable g : N -> N -> N
Infixl 10 ++ : f
Infixl 10 ++ : g
Show true ++ false ++ true
SetOption lean::pp::notation false
Show true ++ false ++ true
Variable a : N
Variable b : N
Show a ++ b ++ a
Show true ++ false ++ false