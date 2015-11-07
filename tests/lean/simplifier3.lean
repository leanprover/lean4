/- Basic rewriting with eq and generic congruence, with no conditionals -/

namespace test_congr

universe l
constant T : Type.{l}
constants (x y z : T → T) (f g h : (T →  T) → (T →  T)) (a b c : T)
constants (Hfxgy : f x = g y) (Hgyhz : g y = h z) (Hab : a = b) (Hbc : b = c)


attribute Hfxgy [simp]
attribute Hgyhz [simp]
attribute Hab [simp]
attribute Hbc [simp]

#simplify eq 2 (f x a) -- h z c

end test_congr

namespace test_congr_fun

universes l1 l2
constants (T : Type.{l1}) (U : T → Type.{l2})
constants (f g : Π (x:T), U x) (x y : T)
constants (Hfg : f = g) (Hxy : x = y)

attribute Hfg [simp]
attribute Hxy [simp]

#simplify eq 2 (f x)
end test_congr_fun
