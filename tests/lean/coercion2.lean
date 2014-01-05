Variable T : Type
Variable R : Type
Variable t2r : T -> R
Coercion t2r
Variable g : R -> R -> R
Variable a : T
print g a a
Variable b : R
print g a b
print g b a
SetOption lean::pp::coercion true
print g a a
print g a b
print g b a
SetOption lean::pp::coercion false
Variable S : Type
Variable s : S
Variable r : S
Variable h : S -> S -> S
Infixl 10 ++ : g
Infixl 10 ++ : h
SetOption lean::pp::notation false
print a ++ b ++ a
print r ++ s ++ r
Check a ++ b ++ a
Check r ++ s ++ r
SetOption lean::pp::coercion true
print a ++ b ++ a
print r ++ s ++ r
SetOption lean::pp::notation true
print a ++ b ++ a
print r ++ s ++ r
