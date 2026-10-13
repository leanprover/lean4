/-!
Tests for the `Nat → Int` cast and relation homomorphisms in `grind`, ported from the
intblasting prototype test suite (#15224).

Verifies that `Int.natCast_add`, `Int.natCast_mul`, `Int.natCast_pow`, `Int.natCast_shiftLeft`,
`Int.natCast_inj`, `Int.ofNat_le`, and `Int.ofNat_lt` are automatically picked up by `grind`
across mixed arithmetic.
-/

example (a b c d s : Nat)
    (h_add : ((a + b : Nat) : Int) = 100)
    (h_mul : ((c * d : Nat) : Int) = 50)
    (h_pow : ((a ^ 2 : Nat) : Int) = 25)
    (h_shift : ((c <<< s : Nat) : Int) = 16)
    (h_le : ((a : Int) ≤ (b : Int)))
    (h_lt : ((c : Int) < (d : Int))) :
    (a : Int) + (b : Int) = 100 ∧
    (c : Int) * (d : Int) = 50 ∧
    (a : Int) ^ 2 = 25 ∧
    (c : Int) <<< s = 16 ∧
    a ≤ b ∧
    c < d := by
  grind

example (x y : Nat) (h : ((x : Int) = (y : Int))) : x = y := by
  grind
