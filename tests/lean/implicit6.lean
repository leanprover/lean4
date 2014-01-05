import Int.
variable f {A : Type} : A -> A -> A
infixl 65 + : f
print true + false
print 10 + 20
print 10 + (- 20)
setoption pp::notation false
setoption pp::coercion true
print true + false
print 10 + 20
print 10 + (- 20)
