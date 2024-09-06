/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki, Leonardo de Moura, Mario Carneiro, Alex Keizer, Harun Khan, Abdalrhman M Mohamed
-/
prelude
import Init.Data.Fin.Basic

set_option linter.missingDocs true

namespace BitVec

section Nat

/-- The `BitVec` with value `i mod 2^n`. -/
@[match_pattern]
protected def ofNat (n : Nat) (i : Nat) : BitVec n where
  toFin := Fin.ofNat' i (Nat.two_pow_pos n)

instance instOfNat : OfNat (BitVec n) i where ofNat := .ofNat n i

/-- Return the bound in terms of toNat. -/
theorem isLt (x : BitVec w) : x.toNat < 2^w := x.toFin.isLt

end Nat

end BitVec
