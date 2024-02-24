/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic

namespace Lean.Meta

/-!
Helper functions for recognizing builtin literal values.
This module focus on recognizing the standard representation used in Lean for these literals.
It also provides support for the following exceptional cases.
- Raw natural numbers (i.e., natural numbers which are not encoded using `OfNat.ofNat`).
- Bit-vectors encoded using `OfNat.ofNat` and `BitVec.ofNat`.
- Negative integers encoded using raw natural numbers.
- Characters encoded `Char.ofNat n` where `n` can be a raw natural number or an `OfNat.ofNat`.
-/

/-- Returns `some n` if `e` is a raw natural number, i.e., it is of the form `.lit (.natVal n)`. -/
def getRawNatValue? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => none

/-- Return `some (n, type)` if `e` is an `OfNat.ofNat`-application encoding `n` for a type with name `typeDeclName`. -/
def getOfNatValue? (e : Expr) (typeDeclName : Name) : MetaM (Option (Nat × Expr)) := OptionT.run do
  guard <| e.isAppOfArity ``OfNat.ofNat 3
  let type ← whnfD e.appFn!.appFn!.appArg!
  guard <| type.getAppFn.isConstOf typeDeclName
  let .lit (.natVal n) := e.appFn!.appArg! | failure
  return (n, type)

/-- Return `some n` if `e` is a raw natural number or an `OfNat.ofNat`-application encoding `n`. -/
def getNatValue? (e : Expr) : MetaM (Option Nat) := do
  if let some n := getRawNatValue? e then
    return some n
  let some (n, _) ← getOfNatValue? e ``Nat | return none
  return some n

/-- Return `some i` if `e` `OfNat.ofNat`-application encoding an integer, or `Neg.neg`-application of one. -/
def getIntValue? (e : Expr) : MetaM (Option Int) := do
  if let some (n, _) ← getOfNatValue? e ``Int then
    return some n
  if e.isAppOfArity ``Neg.neg 3 then
    let some (n, _) ← getOfNatValue? e.appArg! ``Int | return none
    return some (-n)
  return none

/-- Return `some c` if `e` is a `Char.ofNat`-application encoding character `c`. -/
def getCharValue? (e : Expr) : MetaM (Option Char) := OptionT.run do
  guard <| e.isAppOfArity ``Char.ofNat 1
  let n ← getNatValue? e.appArg!
  return Char.ofNat n

/-- Return `some s` if `e` is of the form `.lit (.strVal s)`. -/
def getStringValue? (e : Expr) : (Option String) :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- Return `some ⟨n, v⟩` if `e` is af `OfNat.ofNat` application encoding a `Fin n` with value `v` -/
def getFinValue? (e : Expr) : MetaM (Option ((n : Nat) × Fin n)) := OptionT.run do
  let (v, type) ← getOfNatValue? e ``Fin
  let n ← getNatValue? (← whnfD type.appArg!)
  match n with
  | 0 => failure
  | m+1 => return ⟨m+1, Fin.ofNat v⟩

/-- Return `some ⟨n, v⟩` if `e` is af `OfNat.ofNat` application encoding a `BitVec n` with value `v` -/
def getBitVecValue? (e : Expr) : MetaM (Option ((n : Nat) × BitVec n)) := OptionT.run do
  if e.isAppOfArity ``BitVec.ofNat 2 then
    let n ← getNatValue? e.appFn!.appArg!
    let v ← getNatValue? e.appArg!
    return ⟨n, BitVec.ofNat n v⟩
  let (v, type) ← getOfNatValue? e ``BitVec
  IO.println v
  let n ← getNatValue? (← whnfD type.appArg!)
  return ⟨n, BitVec.ofNat n v⟩

/-- Return `some n` if `e` is an `OfNat.ofNat`-application encoding the `UInt8` with value `n`. -/
def getUInt8Value? (e : Expr) : MetaM (Option UInt8) := OptionT.run do
  let (n, _) ← getOfNatValue? e ``UInt8
  return UInt8.ofNat n

/-- Return `some n` if `e` is an `OfNat.ofNat`-application encoding the `UInt16` with value `n`. -/
def getUInt16Value? (e : Expr) : MetaM (Option UInt16) := OptionT.run do
  let (n, _) ← getOfNatValue? e ``UInt16
  return UInt16.ofNat n

/-- Return `some n` if `e` is an `OfNat.ofNat`-application encoding the `UInt32` with value `n`. -/
def getUInt32Value? (e : Expr) : MetaM (Option UInt32) := OptionT.run do
  let (n, _) ← getOfNatValue? e ``UInt32
  return UInt32.ofNat n

/-- Return `some n` if `e` is an `OfNat.ofNat`-application encoding the `UInt64` with value `n`. -/
def getUInt64Value? (e : Expr) : MetaM (Option UInt64) := OptionT.run do
  let (n, _) ← getOfNatValue? e ``UInt64
  return UInt64.ofNat n

end Lean.Meta
