/- Basic rewriting with eq without congruence or conditionals -/
universe l
constant T : Type.{l}
constants (x y z : T) (f g h : T → T) 
constants (Hfxgy : f x = g y) (Hgyhz : g y = h z)

attribute Hfxgy [simp]
#simplify eq 2 (f x)
attribute Hgyhz [simp]
#simplify eq 2 (f x)
