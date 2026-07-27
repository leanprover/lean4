module
-- Test that grind can solve equations over Fin 2 using PowIdentity
-- The PowIdentity instance for Fin 2 gives x^2 = x, which the ring solver
-- uses to reduce high-degree polynomials.

example (x y : Fin 2) : (x + y)^2 = x + y := by grind
example (x : Fin 2) : x^2 = x := by grind
example (x y : Fin 2) : x^2 + y^2 = x + y := by grind
example (x y : Fin 2) : x * y + x * y = 0 := by grind
example (x y : Fin 2) : (x + y)^2 = x^2 + y^2 := by grind

-- Higher powers reduced by PowIdentity
example (x : Fin 2) : x^4 = x := by grind
example (x : Fin 2) : x^8 = x := by grind

-- Note: `(x + y)^2 = x^128 + y^2` (the motivating example from #12842) does not yet work.
-- The `ToInt` module lifts `Fin 2` expressions to integers and expands `x^128` via the
-- binomial theorem before the `Fin 2` ring solver can reduce it, causing blowup.
