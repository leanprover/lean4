/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic
import Init.Control.Option

namespace Lean.Meta

/-!
Helper functions for recognizing builtin literal values.
This module focus on recognizing the standard representation used in Lean for these literals.
It also provides support for the following exceptional cases.
- Raw natural numbers (i.e., natural numbers which are not encoded using `OfNat.ofNat`).
- Bit-vectors encoded using `OfNat.ofNat` and `BitVec.ofNat`.
- Negative integers encoded using raw natural numbers.
- Characters encoded `Char.ofNat n` where `n` can be a raw natural number or an `OfNat.ofNat`.
- Nested `Expr.mdata`.
-/

/-- Returns `some n` if `e` is a raw natural number, i.e., it is of the form `.lit (.natVal n)`. -/
def getRawNatValue? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | _ => none

/-- Return `some (n, type)` if `e` is an `OfNat.ofNat`-application encoding `n` for a type with name `typeDeclName`. -/
def getOfNatValue? (e : Expr) (typeDeclName : Name) : MetaM (Option (Nat × Expr)) := OptionT.run do
  let_expr OfNat.ofNat type n _ ← e | failure
  let type ← whnfD type
  guard <| type.getAppFn.isConstOf typeDeclName
  let .lit (.natVal n) := n.consumeMData | failure
  return (n, type)

/-- Return `some n` if `e` is a raw natural number or an `OfNat.ofNat`-application encoding `n`. -/
def getNatValue? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if let some n := getRawNatValue? e then
    return some n
  let some (n, _) ← getOfNatValue? e ``Nat | return none
  return some n

/-- Return `some i` if `e` `OfNat.ofNat`-application encoding an integer, or `Neg.neg`-application of one. -/
def getIntValue? (e : Expr) : MetaM (Option Int) := do
  if let some (n, _) ← getOfNatValue? e ``Int then
    return some n
  let_expr Neg.neg _ _ a ← e | return none
  let some (n, _) ← getOfNatValue? a ``Int | return none
  return some (-↑n)

/-- Return `some c` if `e` is a `Char.ofNat`-application encoding character `c`. -/
def getCharValue? (e : Expr) : MetaM (Option Char) := do
  let_expr Char.ofNat n ← e | return none
  let some n ← getNatValue? n | return none
  return some (Char.ofNat n)

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

/--
Return `some ⟨n, v⟩` if `e` is:
- an `OfNat.ofNat` application
- a `BitVec.ofNat` application
- a `BitVec.ofNatLt` application
that encode a `BitVec n` with value `v`.
-/
def getBitVecValue? (e : Expr) : MetaM (Option ((n : Nat) × BitVec n)) := OptionT.run do
  match_expr e with
  | BitVec.ofNat nExpr vExpr =>
    let n ← getNatValue? nExpr
    let v ← getNatValue? vExpr
    return ⟨n, BitVec.ofNat n v⟩
  | BitVec.ofNatLt nExpr vExpr _ =>
    let n ← getNatValue? nExpr
    let v ← getNatValue? vExpr
    return ⟨n, BitVec.ofNat n v⟩
  | _ =>
    let (v, type) ← getOfNatValue? e ``BitVec
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

-- TODO: extensibility

/--
If `e` is a literal value, ensure it is encoded using the standard representation.
Otherwise, just return `e`.
-/
def normLitValue (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some n ← getNatValue? e then return toExpr n
  if let some n ← getIntValue? e then return toExpr n
  if let some ⟨_, n⟩ ← getFinValue? e then return toExpr n
  if let some ⟨_, n⟩ ← getBitVecValue? e then return toExpr n
  if let some s := getStringValue? e then return toExpr s
  if let some c ← getCharValue? e then return toExpr c
  if let some n ← getUInt8Value? e then return toExpr n
  if let some n ← getUInt16Value? e then return toExpr n
  if let some n ← getUInt32Value? e then return toExpr n
  if let some n ← getUInt64Value? e then return toExpr n
  return e

/--
Returns `true` if `e` is a literal value.
-/
def isLitValue (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  if (← getNatValue? e).isSome then return true
  if (← getIntValue? e).isSome then return true
  if (← getFinValue? e).isSome then return true
  if (← getBitVecValue? e).isSome then return true
  if (getStringValue? e).isSome then return true
  if (← getCharValue? e).isSome then return true
  if (← getUInt8Value? e).isSome then return true
  if (← getUInt16Value? e).isSome then return true
  if (← getUInt32Value? e).isSome then return true
  if (← getUInt64Value? e).isSome then return true
  return false

/--
If `e` is a `Nat`, `Int`, or `Fin` literal value, converts it into a constructor application.
Otherwise, just return `e`.
-/
-- TODO: support other builtin literals if needed
def litToCtor (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some n ← getNatValue? e then
    if n = 0 then
      return mkConst ``Nat.zero
    else
      return .app (mkConst ``Nat.succ) (toExpr (n-1))
  if let some n ← getIntValue? e then
    if n < 0 then
      return .app (mkConst ``Int.negSucc) (toExpr (- (n+1)).toNat)
    else
      return .app (mkConst ``Int.ofNat) (toExpr n.toNat)
  if let some ⟨n, v⟩ ← getFinValue? e then
    let i := toExpr v.val
    let n := toExpr n
    -- Remark: we construct the proof manually here to avoid a cyclic dependency.
    let p := mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) i n
    let h := mkApp3 (mkConst ``of_decide_eq_true) p
      (mkApp2 (mkConst ``Nat.decLt) i n)
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true))
    return mkApp3 (mkConst ``Fin.mk) n i h
  return e

/--
Check if an expression is a list literal (i.e. a nested chain of `List.cons`, ending at a `List.nil`),
where each element is "recognised" by a given function `f : Expr → MetaM (Option α)`,
and return the array of recognised values.
-/
partial def getListLitOf? (e : Expr) (f : Expr → MetaM (Option α)) : MetaM (Option (Array α)) := do
  let mut e ← instantiateMVars e.consumeMData
  let mut r := #[]
  while true do
    match_expr e with
    | List.nil _ => break
    | List.cons _ a as => do
      let some a ← f a | return none
      r := r.push a
      e := as
    | _ => return none
  return some r

/--
Check if an expression is a list literal (i.e. a nested chain of `List.cons`, ending at a `List.nil`),
returning the array of `Expr` values.
-/
def getListLit? (e : Expr) : MetaM (Option (Array Expr)) := getListLitOf? e fun s => return some s

/--
Check if an expression is an array literal
(i.e. `List.toArray` applied to a nested chain of `List.cons`, ending at a `List.nil`),
where each element is "recognised" by a given function `f : Expr → MetaM (Option α)`,
and return the array of recognised values.
-/
def getArrayLitOf? (e : Expr) (f : Expr → MetaM (Option α)) : MetaM (Option (Array α)) := do
  let e ← instantiateMVars e.consumeMData
  match_expr e with
  | List.toArray _ as => getListLitOf? as f
  | _ => return none

/--
Check if an expression is an array literal
(i.e. `List.toArray` applied to a nested chain of `List.cons`, ending at a `List.nil`),
returning the array of `Expr` values.
-/
def getArrayLit? (e : Expr) : MetaM (Option (Array Expr)) := getArrayLitOf? e fun s => return some s


end Lean.Meta
