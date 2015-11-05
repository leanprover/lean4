/- Basic rewriting with eq without congruence or conditionals -/
universe l
constant T : Type.{l}
constants (x y z : T) (f g h : T → T) 
constants (Hfxgy : f x = g y) (Hgyhz : g y = h z)

#simplify eq 2 (f x) -- f x

attribute Hfxgy [simp]
attribute Hgyhz [simp]

set_option simplify.exhaustive false
#simplify eq 2 (f x) -- g y

set_option simplify.exhaustive true
#simplify eq 2 (f x) -- h z
