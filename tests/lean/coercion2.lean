variable T : Type
variable R : Type
variable t2r : T -> R
coercion t2r
variable g : R -> R -> R
variable a : T
print g a a
variable b : R
print g a b
print g b a
setoption lean::pp::coercion true
print g a a
print g a b
print g b a
setoption lean::pp::coercion false
variable S : Type
variable s : S
variable r : S
variable h : S -> S -> S
infixl 10 ++ : g
infixl 10 ++ : h
setoption lean::pp::notation false
print a ++ b ++ a
print r ++ s ++ r
check a ++ b ++ a
check r ++ s ++ r
setoption lean::pp::coercion true
print a ++ b ++ a
print r ++ s ++ r
setoption lean::pp::notation true
print a ++ b ++ a
print r ++ s ++ r
