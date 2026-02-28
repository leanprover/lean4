def   double (n :   Nat) : Nat :=    n * 2

-- Tripling is useful for tests

def triple   (n : Nat) :   Nat := n *   3

/-! ## Combining functions -/

def   six : Nat :=
  triple   (double 1)
--^ formatting
