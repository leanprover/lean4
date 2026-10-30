module

import Init.Data.Nat.ExtendedGcd

/-!
Tests `Nat.extendedGcd` from compiled and interpreted callers, with retained operands and results
whose gcd and both signed coefficients require heap allocation.
-/

private def values (seed : Nat) : Array Nat :=
  #[0, 1, 2, 3, 65535, 65536, 65537,
    2 ^ 31 - 1, 2 ^ 31, 2 ^ 31 + 1, 2 ^ 31 + 3,
    2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 32 + 3,
    2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
    2 ^ 128 - 1, 2 ^ 128, 2 ^ 128 + 1, 2 ^ 256 - 1, 2 ^ 256 + 1].map (· + seed)

public def main (args : List String) : IO Unit := do
  -- Depend on runtime input so the calls are not evaluated during module initialization.
  let inputs := values args.length
  for g in #[1, 2 ^ 64] do
    for x in inputs do
      for y in inputs do
        let a := x * g
        let b := y * g
        let r := Nat.extendedGcd a b
        let expected := Nat.extendedGcd.go a 1 0 b 0 1
        unless r = expected && r.gcd = Nat.gcd a b &&
            (r.gcd : Int) = a * r.coeffA + b * r.coeffB do
          throw <| IO.userError s!"extendedGcd disagrees on ({a}, {b}): {repr r}, expected {repr expected}"
