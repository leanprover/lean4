Import Int
Import Real
print 1 + true
Variable R : Type
Variable T : Type
Variable r2t : R -> T
Coercion r2t
Variable t2r : T -> R
Coercion t2r
Variable f : T -> R -> T
Variable a : T
Variable b : R
SetOption lean::pp::coercion true
SetOption lean::pp::notation false
print f a b
print f b a
Variable g : R -> T -> R
Infix 10 ++ : f
Infix 10 ++ : g
print a ++ b
print b ++ a
