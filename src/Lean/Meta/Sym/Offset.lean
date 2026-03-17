/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.LitValues
public section
namespace Lean.Meta.Sym
/-!
# Offset representation for natural number expressions

This module provides utilities for representing `Nat` expressions in the form `e + k`,
where `e` is an arbitrary expression and `k` is a constant.
This normalization is used during pattern matching and unification.
-/

/--
Represents a natural number expression as a base plus a constant offset.
- `.num k` represents the literal `k`
- `.add e k` represents `e + k`

Used for pattern matching and unification.
-/
inductive Offset where
  | num (k : Nat)
  | add (e : Expr) (k : Nat)
  deriving Inhabited

/-- Increments the constant part of the offset by `k'`. -/
def Offset.inc : Offset → Nat → Offset
  | .num k,   k' => .num (k+k')
  | .add e k, k' => .add e (k+k')

/--
Returns `some offset` if `e` is an offset term. That is, it is of the form
- `Nat.succ a`, OR
- `a + k` where `k` is a numeral.

Assumption: standard instances are used for `OfNat Nat n` and `HAdd Nat Nat Nat`
-/
partial def isOffset? (e : Expr) : OptionT Id Offset :=
  match_expr e with
  | Nat.succ a => do
    return get a |>.inc 1
  | HAdd.hAdd α _ _ _ a b => do
    guard (α.isConstOf ``Nat)
    let n ← getNatValue? b
    return get a |>.inc n
  | _ => failure
where
  get (e : Expr) : Offset :=
    isOffset? e |>.getD (.add e 0)

/-- Variant of `isOffset?` that first checks if `declName` is `Nat.succ` or `HAdd.hAdd`. -/
def isOffset?' (declName : Name) (p : Expr) : OptionT Id Offset := do
  guard (declName == ``Nat.succ || declName == ``HAdd.hAdd)
  isOffset? p

/--  Returns `true` if `e` is an offset term.-/
partial def isOffset (e : Expr) : Bool :=
  match_expr e with
  | Nat.succ _ => true
  | HAdd.hAdd α _ _ _ _ b =>
    α.isConstOf ``Nat &&
    match_expr b with
    | OfNat.ofNat _ n _ => (n matches .lit (.natVal _))
    | _ => false
  | _ => false

/-- Variant of `isOffset?` that first checks if `declName` is `Nat.succ` or `HAdd.hAdd`. -/
def isOffset' (declName : Name) (p : Expr) : Bool :=
  (declName == ``Nat.succ || declName == ``HAdd.hAdd) && isOffset p

/--
Converts the given expression into an offset.
Assumptions:
- `e` has type `Nat`.
- standard instances are used for `OfNat Nat n` and `HAdd Nat Nat Nat`.
-/
partial def toOffset (e : Expr) : Offset :=
  match_expr e with
  | Nat.succ a => toOffset a |>.inc 1
  | HAdd.hAdd _ _ _ _ a b => Id.run do
    let some n := getNatValue? b | .add e 0
    toOffset a |>.inc n
  | OfNat.ofNat _ n _ => Id.run do
    let .lit (.natVal n) := n | .add e 0
    .num n
  | _ => .add e 0

end Lean.Meta.Sym
