Set pp::colors false
Variable T : Type
Variable R : Type
Variable t2r : T -> R
Coercion t2r
Variable g : R -> R -> R
Variable a : T
Show g a a
Variable b : R
Show g a b
Show g b a
Set lean::pp::coercion true
Show g a a
Show g a b
Show g b a
Set lean::pp::coercion false
Variable S : Type
Variable s : S
Variable r : S
Variable h : S -> S -> S
Infixl 10 ++ : g
Infixl 10 ++ : h
Set lean::pp::notation false
Show a ++ b ++ a
Show r ++ s ++ r
Check a ++ b ++ a
Check r ++ s ++ r
Set lean::pp::coercion true
Show a ++ b ++ a
Show r ++ s ++ r
Set lean::pp::notation true
Show a ++ b ++ a
Show r ++ s ++ r
