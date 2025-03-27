/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Message

namespace Lean.Meta.Grind.Arith

/-- Returns `true` if `e` is of the form `Nat` -/
def isNatType (e : Expr) : Bool :=
  e.isConstOf ``Nat

/-- Returns `true` if `e` is of the form `@instHAdd Nat instAddNat` -/
def isInstAddNat (e : Expr) : Bool :=
  let_expr instHAdd a b := e | false
  isNatType a && b.isConstOf ``instAddNat

/-- Returns `true` if `e` is `instLENat` -/
def isInstLENat (e : Expr) : Bool :=
  e.isConstOf ``instLENat

/--
Returns `some (a, b)` if `e` is of the form
```
@HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) a b
```
-/
def isNatAdd? (e : Expr) : Option (Expr × Expr) :=
  let_expr HAdd.hAdd _ _ _ i a b := e | none
  if isInstAddNat i then some (a, b) else none

/--
Returns `true` if `e` is of the form
```
@HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) _ _
```
-/
def isNatAdd (e : Expr) : Bool :=
  let_expr HAdd.hAdd _ _ _ i _ _ := e | false
  isInstAddNat i

/-- Returns `some k` if `e` `@OfNat.ofNat Nat _ (instOfNatNat k)` -/
def isNatNum? (e : Expr) : Option Nat := Id.run do
  let_expr OfNat.ofNat _ _ inst := e | none
  let_expr instOfNatNat k := inst | none
  let .lit (.natVal k) := k | none
  some k


end Lean.Meta.Grind.Arith
