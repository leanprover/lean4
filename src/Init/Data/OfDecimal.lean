/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Float
import Init.Data.Nat

/- For decimal numbers (e.g., `1.23`).
   Examples:
   - `OfDecimal.ofDecimal 123 true 2`    represents `1.23`
   - `Ofdecimal.ofdecimal 121 false 100` represents `121e100`
-/
class OfDecimal (α : Type u) where
  ofDecimal : Nat → Bool → Nat → α

@[defaultInstance]
instance : OfDecimal Float where
  ofDecimal m s e := Float.ofDecimal m s e
