/-!
Tests big `Nat` multiplication and division on large and unbalanced operands, which use Karatsuba
multiplication and Newton division (`Init.Data.Nat.Big`). The expected output was produced with the
former GMP-based implementation.
-/

def P : Nat := 2^61 - 1

def digest (n : Nat) : String := s!"{n % P} {n.log2}"

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def main : IO Unit := do
  let a := 3^200000
  let b := 7^150000
  IO.println (digest (a * b))
  IO.println (digest ((2^100000 - 1) * (2^100000 - 1)))
  IO.println (digest ((2^200000 - 1) * (2^3001 + 12345)))
  IO.println (digest (a * 1000000007))
  IO.println (digest (fact 4000))
  IO.println (digest ((a * b + 17) / b))
  IO.println (digest ((a * b + 17) % a))
  IO.println (digest ((a * b) / (2^5000 + 1)))
  IO.println (Nat.gcd (a * 2^1000) (b * 6^500) == 3^500 * 2^500)
  IO.println (toString (fact 1000)).length
  -- Newton division: exact multiples, remainder `b - 1`, and divisors `2^k - 1` and `2^k`
  let c := 5^60000
  IO.println (digest ((a * c) / c))
  IO.println (digest ((a * c + c - 1) / c))
  IO.println (digest ((a * c + c - 1) % c))
  IO.println (digest (b / (2^30000 - 1)))
  IO.println (digest (b % (2^30000 - 1)))
  IO.println (digest (b / 2^40000))
  IO.println (digest ((a * a) / (a + 1)))
  IO.println (digest ((a * a) % (a + 1)))
  -- quotient just above the threshold
  IO.println (digest ((c * 2^24600 + 3) / c))
