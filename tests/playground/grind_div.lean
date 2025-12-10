import Init.Data.Nat.Div.Basic

/--
This example tests the grind annotation on `mod_eq_of_lt`.
-/
example {a b : Nat} : a < b → a % b = a := by grind
