/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Coe
public import Init.Data.OfScientific

public section

/-!
In this file, we define the coercion `α → Option α`.

The use of this coercion is **banned** in `Init` and `Std` (but allowed everywhere else). For this
reason, we define it in this file, which must not be imported anywhere in `Init` or `Std` (this
is enforced by the test `importStructure.lean`).
-/

instance optionCoe {α : Type u} : Coe α (Option α) where
  coe := some

/--
The coercion-to-option-type behavior provided by `optionCoe` does not work for natural number
literals or floating point literals because of the automatic insertion of `OfNat` and `OfScientific`
coercions around these literals.

This instance provides the corresponding coercion for natural number literals.
-/
instance natOptionCoe {α : Type u} {n : Nat} [OfNat α n] : OfNat (Option α) n where
  ofNat := some (OfNat.ofNat n)

/--
The coercion-to-option-type behavior provided by `optionCoe` does not work for natural number
literals or floating point literals because of the automatic insertion of `OfNat` and `OfScientific`
coercions around these literals.

This instance provides the corresponding coercion for scientific number literals.
-/
instance scientificOptionCoe {α : Type u} [OfScientific α] : OfScientific (Option α) where
  ofScientific (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) :=
    some (OfScientific.ofScientific mantissa exponentSign decimalExponent)
