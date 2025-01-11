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

/-- Returns `some k` if `e` `@OfNat.ofNat Nat _ (instOfNatNat k)` -/
def isNatNum? (e : Expr) : Option Nat := Id.run do
  let_expr OfNat.ofNat _ _ inst := e | none
  let_expr instOfNatNat k := inst | none
  let .lit (.natVal k) := k | none
  some k

/-- Returns `some (a, k)` if `e` is of the form `a + k`.  -/
def isNatOffset? (e : Expr) : Option (Expr × Nat) := Id.run do
  let some (a, b) := isNatAdd? e | none
  let some k := isNatNum? b | none
  some (a, k)

/-- An offset constraint. -/
structure Offset.Cnstr (α : Type) where
  a  : α
  b  : α
  k  : Int := 0
  le : Bool := true
  deriving Inhabited

def Offset.Cnstr.neg : Cnstr α → Cnstr α
  | { a, b, k, le } => { b, a, le, k := k + 1 }

def Offset.toMessageData [inst : ToMessageData α] (c : Offset.Cnstr α) : MessageData :=
  match c.k, c.le with
  | .ofNat 0,   true  => m!"{c.a} ≤ {c.b}"
  | .ofNat 0,   false => m!"{c.a} = {c.b}"
  | .ofNat k,   true  => m!"{c.a} + {k} ≤ {c.b}"
  | .ofNat k,   false => m!"{c.a} + {k} = {c.b}"
  | .negSucc k, true  => m!"{c.a} ≤ {c.b} + {k + 1}"
  | .negSucc k, false => m!"{c.a} = {c.b} + {k + 1}"

instance : ToMessageData (Offset.Cnstr Expr) where
  toMessageData c := Offset.toMessageData c

/-- Returns `some cnstr` if `e` is offset constraint. -/
def isNatOffsetCnstr? (e : Expr) : Option (Offset.Cnstr Expr) :=
  match_expr e with
  | LE.le _ inst a b => if isInstLENat inst then go a b true else none
  | Eq α a b => if isNatType α then go a b false else none
  | _ => none
where
  go (a b : Expr) (le : Bool) :=
    if let some (a, k) := isNatOffset? a then
      some { a, k, b, le }
    else if let some (b, k) := isNatOffset? b then
      some { a, b, k := - k, le }
    else
      some { a, b, le }

end Lean.Meta.Grind.Arith
