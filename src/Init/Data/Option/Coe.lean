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

/-!
The coercion to `Option` types provided by `optionCoe` does not work for numeric literals because
of the way numeric literals are automatically wrapped in a call to `OfNat.ofNat`: Lean expands the
the literal `5` to the syntax `OfNat.ofNat (α := _) (nat_lit 5)` unless it's preceded by `nat_lit`.

Without the following typeclass instances, `(5 : Option Nat)` fails at typeclass inference, even
though `(OfNat.ofNat (α := Nat) (nat_lit 5) : Option Nat)` would succeed, with the help of a type
coercion, via the `optionCoe` instance and inserting a type coercion. While these definitions do
not involve type coercion, they result in Lean behaving more uniformly in the presence of
`optionCoe`.
-/

/--
If the natural number n can be used as an expression of α via `OfNat.ofNat`, then it can also be
used an expression of type `Option α`.
-/
instance {α : Type u} {n : Nat} [OfNat α n] : OfNat (Option α) n where
  ofNat := some (OfNat.ofNat n)

/--
If an scientific number can be used as an expression of α via `OfScientific.ofScientific`, then it
can also be used an expression of type `Option α`.
-/
instance scientificOptionCoe {α : Type u} [OfScientific α] : OfScientific (Option α) where
  ofScientific (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) :=
    some (OfScientific.ofScientific mantissa exponentSign decimalExponent)
