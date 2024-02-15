prelude
import Init.Data.Int.Basic
import Init.Data.Nat.Gcd

namespace Int

/-! ## gcd -/

/-- Computes the greatest common divisor of two integers, as a `Nat`. -/
def gcd (m n : Int) : Nat := m.natAbs.gcd n.natAbs

end Int
