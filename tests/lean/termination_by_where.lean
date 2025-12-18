/-!
This module systematically tests the relative placement of `decreasing_by` and `where`.
-/

-- For concise recursive definition that need well-founded recursion
-- and `decreasing_by` tactics that would fail if run on the wrong function
opaque dec1 : Nat → Nat
axiom dec1_lt (n : Nat) : dec1 n < n
opaque dec2 : Nat → Nat
axiom dec2_lt (n : Nat) : dec2 n < n

def foo (n : Nat) := foo (dec1 n) + bar n
decreasing_by apply dec1_lt
where
bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt
