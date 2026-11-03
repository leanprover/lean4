/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Std.Data.Nat.Big.Basic
public import Std.Data.Nat.Big.Knuth
public import Std.Data.Nat.Big.Div
public import Std.Data.Nat.Big.Karatsuba
public import Std.Data.Nat.Big.Newton
public import Std.Data.Nat.Big.Bits
public import Std.Data.Nat.Big.Algo
public import Std.Data.Nat.Big.Decimal

/-!
# Correctness of big number arithmetic

The runtime implements big `Nat` and `Int` arithmetic in Lean, on the magnitudes of
`Init.Data.Nat.Big`. These modules prove each operation correct with respect to `Nat`: for
normalized inputs whose result fits the size bound `Nat.Big.maxBytes`, every operation computes the
corresponding `Nat` function, and returns a normalized magnitude.
-/
