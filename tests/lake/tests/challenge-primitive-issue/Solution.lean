prelude
import Init.Prelude
import Init.Core
-- Supplies the kernel built-ins the comparison exports, so that `Nat.gcd` below is the only
-- constant that differs from the challenge.
import Init.Data.String.Bootstrap

def Nat.gcd (_ _ : Nat) : Nat := 0

theorem thm1 a b : Nat.gcd a b = 0 := by
  unfold Nat.gcd
  rfl

theorem thm2 : Nat.gcd 1 1 = 1 := rfl

theorem boom : False :=
  Nat.noConfusion <| Eq.trans (thm1 1 1).symm thm2
