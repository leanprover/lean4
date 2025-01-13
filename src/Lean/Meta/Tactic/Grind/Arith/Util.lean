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
  u  : α
  v  : α
  k  : Int := 0
  le : Bool := true
  deriving Inhabited

def Offset.Cnstr.neg : Cnstr α → Cnstr α
  | { u, v, k, le } => { u := v, v := u, le, k := -k - 1 }

example (c : Offset.Cnstr α) : c.neg.neg = c := by
  cases c; simp [Offset.Cnstr.neg]; omega

def Offset.toMessageData [inst : ToMessageData α] (c : Offset.Cnstr α) : MessageData :=
  match c.k, c.le with
  | .ofNat 0,   true  => m!"{c.u} ≤ {c.v}"
  | .ofNat 0,   false => m!"{c.u} = {c.v}"
  | .ofNat k,   true  => m!"{c.u} ≤ {c.v} + {k}"
  | .ofNat k,   false => m!"{c.u} = {c.v} + {k}"
  | .negSucc k, true  => m!"{c.u} + {k + 1} ≤ {c.v}"
  | .negSucc k, false => m!"{c.u} + {k + 1} = {c.v}"

instance : ToMessageData (Offset.Cnstr Expr) where
  toMessageData c := Offset.toMessageData c

/-- Returns `some cnstr` if `e` is offset constraint. -/
def isNatOffsetCnstr? (e : Expr) : Option (Offset.Cnstr Expr) :=
  match_expr e with
  | LE.le _ inst a b => if isInstLENat inst then go a b true else none
  | Eq α a b => if isNatType α then go a b false else none
  | _ => none
where
  go (u v : Expr) (le : Bool) :=
    if let some (u, k) := isNatOffset? u then
      some { u, k := - k, v, le }
    else if let some (v, k) := isNatOffset? v then
      some { u, v, k := k, le }
    else
      some { u, v, le }

end Lean.Meta.Grind.Arith
