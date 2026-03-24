import Lean

/-! Tests for permutation theorem support in `Sym.simp` -/

-- Nat.add_comm is a permutation theorem: x + y = y + x
-- Without perm support, `simp` with this theorem would loop.

register_sym_simp commSimp where
  post := ground >> rewrite [Nat.add_comm]

-- This should terminate: Nat.add_comm is detected as perm,
-- and only applied when result < input.
example (x y : Nat) : x + y = y + x := by
  sym =>
    simp commSimp

-- Combining perm with non-perm theorems
register_sym_simp commZeroSimp where
  post := ground >> rewrite [Nat.add_comm, Nat.zero_add, Nat.add_zero]

example (x y : Nat) : 0 + (x + y) = y + x := by
  sym =>
    simp commZeroSimp

-- Verify perm doesn't interfere with non-perm theorems
register_sym_simp nonPermSimp where
  post := ground >> rewrite [Nat.zero_add]

example (x : Nat) : 0 + x = x := by
  sym =>
    simp nonPermSimp

register_sym_simp simple where
  post := ground

example (x y z w : Nat) : x + y + z + w = w + (z + y) + x := by
  sym => simp simple [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
