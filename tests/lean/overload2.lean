Set pp::colors false
Show 1 + true
Variable R : Type
Variable T : Type
Variable r2t : R -> T
Coercion r2t
Variable t2r : T -> R
Coercion t2r
Variable f : T -> R -> T
Variable a : T
Variable b : R
Set lean::pp::coercion true
Set lean::pp::notation false
Show f a b
Show f b a
Variable g : R -> T -> R
Infix 10 ++ : f
Infix 10 ++ : g
Show a ++ b
Show b ++ a
