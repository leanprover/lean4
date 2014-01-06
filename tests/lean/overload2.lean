import Int
import Real
print 1 + true
variable R : Type
variable T : Type
variable r2t : R -> T
coercion r2t
variable t2r : T -> R
coercion t2r
variable f : T -> R -> T
variable a : T
variable b : R
set::option lean::pp::coercion true
set::option lean::pp::notation false
print f a b
print f b a
variable g : R -> T -> R
infix 10 ++ : f
infix 10 ++ : g
print a ++ b
print b ++ a
