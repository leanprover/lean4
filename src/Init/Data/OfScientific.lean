/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Float
import Init.Data.Nat

/- For decimal and scientific numbers (e.g., `1.23`, `3.12e10`).
   Examples:
   - `OfScientific.ofScientific 123 true 2`    represents `1.23`
   - `OfScientific.ofScientific 121 false 100` represents `121e100`
-/
class OfScientific (α : Type u) where
  ofScientific : Nat → Bool → Nat → α

@[defaultInstance]
instance : OfScientific Float where
  ofScientific m s e := Float.ofScientific m s e
