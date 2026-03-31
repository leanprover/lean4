/-!
# Test that `lia` handles numerals in non-tail positions of polynomials

Regression test: after the canonicalizer change (PR #13166), `Fin` coercions can
produce value-level expressions like `↑n + 1 + 1` where `1` appears as a numeral
in a non-tail position of the polynomial being built by `toPoly`.  Previously,
`addMonomial` would treat such numerals as variables; now it folds them into the
polynomial constant via `Poly.addConst`.
-/
module

example (n : Nat) (i : Fin (n + 1 + 1)) (h : n + 1 + 1 ≤ ↑i + ↑i + 1) :
    ↑i + ↑i + 1 - (n + 1 + 1) < n + 1 + 1 := by
  lia
