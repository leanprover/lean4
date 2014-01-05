Import Int.
Variable f {A : Type} : A -> A -> A
Infixl 65 + : f
print true + false
print 10 + 20
print 10 + (- 20)
SetOption pp::notation false
SetOption pp::coercion true
print true + false
print 10 + 20
print 10 + (- 20)
