/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki, Leonardo de Moura, Mario Carneiro, Alex Keizer, Harun Khan, Abdalrhman M Mohamed
-/
prelude
import Init.Data.Fin.Basic

set_option linter.missingDocs true

/-!
This module exists to provide the very basic `BitVec` definitions required for
`Init.Data.UInt.BasicAux`.
-/

namespace BitVec

section Nat

/-- The `BitVec` with value `i mod 2^n`. -/
@[match_pattern]
protected def ofNat (n : Nat) (i : Nat) : BitVec n where
  toFin := Fin.ofNat' (2^n) i

instance instOfNat : OfNat (BitVec n) i where ofNat := .ofNat n i

/-- Return the bound in terms of toNat. -/
theorem isLt (x : BitVec w) : x.toNat < 2^w := x.toFin.isLt

end Nat

section arithmetic

/--
Addition for bit vectors. This can be interpreted as either signed or unsigned addition
modulo `2^n`.

SMT-Lib name: `bvadd`.
-/
protected def add (x y : BitVec n) : BitVec n := .ofNat n (x.toNat + y.toNat)
instance : Add (BitVec n) := ⟨BitVec.add⟩

/--
Subtraction for bit vectors. This can be interpreted as either signed or unsigned subtraction
modulo `2^n`.
-/
protected def sub (x y : BitVec n) : BitVec n := .ofNat n ((2^n - y.toNat) + x.toNat)
instance : Sub (BitVec n) := ⟨BitVec.sub⟩

end arithmetic

end BitVec
