module

import Init.Data.Nat.ExtendedGcd

/-!
Tests the exported Lean fallback for `Nat.extendedGcd`, including its ownership convention,
on small and large inputs even when GMP is enabled. Inputs remain live after each call.
-/

@[extern "lean_nat_extended_gcd_fallback"]
private def fallback (a b : Nat) : Nat.ExtendedGcdResult :=
  Nat.extendedGcd.go a 1 0 b 0 1

public def main (args : List String) : IO Unit := do
  let inputs := #[0, 1, 2, 3, 65535, 65536, 65537,
    2^31 - 1, 2^31, 2^32 + 1, 2^63 - 1, 2^63, 2^64 + 1,
    2^128 - 1, 2^128 + 1, 2^256 + 1].map (· + args.length)
  for g in #[1, 2^64] do
    for x in inputs do
      for y in inputs do
        let a := x * g
        let b := y * g
        let r := fallback a b
        unless r = Nat.extendedGcd a b && r.gcd = Nat.gcd a b &&
            (r.gcd : Int) = a * r.coeffA + b * r.coeffB do
          throw <| IO.userError s!"extendedGcd fallback disagrees on ({a}, {b}): {repr r}"
