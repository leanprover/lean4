module

public section

class Monoid (M : Type) extends Mul M where

class DivInvMonoid (G : Type) extends Mul G where
  /-- The power operation: `a ^ n = a * ··· * a`; `a ^ (-n) = a⁻¹ * ··· a⁻¹` (`n` times) -/
  protected zpow : Int → G → G
