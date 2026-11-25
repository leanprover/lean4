/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.Data.Nat.Big.Basic
public import Init.Data.Nat.Big.Mul
public import Init.Data.Nat.Big.Div

/-!
# Big natural numbers

The runtime represents a natural number that does not fit into a scalar as a `ByteArray` of
little-endian 32-bit digits without leading zero digits, a `BigNat`. The modules
`Init.Data.Nat.Big.Basic`, `Init.Data.Nat.Big.Mul` and `Init.Data.Nat.Big.Div` implement arithmetic
on `BigNat`s; `Init.Data.Nat.BigRuntime` builds the runtime's big `Nat` and `Int` primitives on top
of them, and `Verif.Init.Data.Nat.Big` in `tests/verif` proves the operations correct.

A `BigNat` bounds its size so that digit offsets never overflow `USize`, and digit accesses carry
their bounds as proofs, which are erased at runtime. The operations must not create big `Nat`s
themselves, as that would call back into them, so all counting at runtime uses `USize`. They are
called while `Init.Prelude` is being initialized, so they must not refer to module-level constants;
closed terms are therefore not extracted.
-/
