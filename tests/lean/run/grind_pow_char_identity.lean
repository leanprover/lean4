-- Test that grind can solve equations over Fin 2 using PowCharIdentity
-- The PowCharIdentity instance for Fin 2 gives x^2 = x, which the ring solver
-- uses to reduce high-degree polynomials.

example (x y : Fin 2) : (x + y)^2 = x + y := by grind
example (x : Fin 2) : x^2 = x := by grind
example (x y : Fin 2) : x^2 + y^2 = x + y := by grind
example (x y : Fin 2) : x * y + x * y = 0 := by grind
example (x y : Fin 2) : (x + y)^2 = x^2 + y^2 := by grind
