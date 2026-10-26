/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
import Init.While
public section
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

/-- Returns `true` if `getNatValue? e` is `some _`. -/
def isNatValue (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if e.isRawNatLit then return true
  let_expr OfNat.ofNat type n _ ← e | return false
  unless n.consumeMData.isRawNatLit do return false
  return (← whnfD type).getAppFn.isConstOf ``Nat

/-- Returns `true` if `getNatValue? e` is `some n` with `n ≠ 0`. -/
def isNonZeroNatValue (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if let .lit (.natVal n) := e then return n != 0
  let_expr OfNat.ofNat type n _ ← e | return false
  let .lit (.natVal n) := n.consumeMData | return false
  if n == 0 then return false
  return (← whnfD type).getAppFn.isConstOf ``Nat

/-- Return `some i` if `e` `OfNat.ofNat`-application encoding an integer, or `Neg.neg`-application of one. -/
def getIntValue? (e : Expr) : MetaM (Option Int) := do
  if let some (n, _) ← getOfNatValue? e ``Int then
    return some n
  let_expr Neg.neg _ _ a ← e | return none
  let some (n, _) ← getOfNatValue? a ``Int | return none
  return some (-↑n)

/-- Return `some b` if `e` is the boolean literal `true` or `false`. -/
private def getBoolLit? (e : Expr) : Option Bool :=
  match e.consumeMData with
  | .const ``Bool.true _  => some true
  | .const ``Bool.false _ => some false
  | _ => none

/-- Recognize a non-negated `Rat` literal: an `OfScientific` or `OfNat` application. -/
private def getRatLit? (e : Expr) : MetaM (Option Rat) := OptionT.run do
  match_expr e with
  | OfScientific.ofScientific type _ m s exp =>
    guard ((← whnfD type).isConstOf ``Rat)
    let some s := getBoolLit? s | failure
    return Rat.ofScientific (← getNatValue? m) s (← getNatValue? exp)
  | _ =>
    let (n, _) ← getOfNatValue? e ``Rat
    return (n : Rat)

/--
Return `some r` if `e` is a rational `OfNat` or `OfScientific` literal, optionally negated,
or a division of an optionally negated `OfNat` literal by an `OfNat` literal.
-/
def getRatValue? (e : Expr) : MetaM (Option Rat) := do
  match_expr e with
  | HDiv.hDiv _ _ _ _ a b =>
    let some n ← getRatValueNum? a | return none
    let some (d, _) ← getOfNatValue? b ``Rat | return none
    return some (n / (d : Rat))
  | Neg.neg _ _ a =>
    let some n ← getRatLit? a | return none
    return some (-n)
  | _ => getRatLit? e
where
  getRatValueNum? (e : Expr) : MetaM (Option Rat) := do
    if let some (n, _) ← getOfNatValue? e ``Rat then
      return some (n : Rat)
    let_expr Neg.neg _ _ a ← e | return none
    let some (n, _) ← getOfNatValue? a ``Rat | return none
    return some (-(n : Rat))

/-- Return `some c` if `e` is a `Char.ofNat`-application that encodes the character `c`. -/
def getCharValue? (e : Expr) : MetaM (Option Char) := do
  let_expr Char.ofNat n ← e | return none
  let some n ← getNatValue? n | return none
  return some (Char.ofNat n)

/-- Return `some s` if `e` is of the form `.lit (.strVal s)`. -/
def getStringValue? (e : Expr) : (Option String) :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- Return `some ⟨n, v⟩` if `e` is an `OfNat.ofNat` application encoding a `Fin n` with value `v` -/
def getFinValue? (e : Expr) : MetaM (Option ((n : Nat) × Fin n)) := OptionT.run do
  let (v, type) ← getOfNatValue? e ``Fin
  let n ← getNatValue? (← whnfD type.appArg!)
  match n with
  | 0 => failure
  | m+1 => return ⟨m+1, Fin.ofNat _ v⟩

/--
Return `some ⟨n, v⟩` if `e` is:
- an `OfNat.ofNat` application
- a `BitVec.ofNat` application
- a `BitVec.ofNatLT` application
that encode a `BitVec n` with value `v`.
-/
def getBitVecValue? (e : Expr) : MetaM (Option ((n : Nat) × BitVec n)) := OptionT.run do
  match_expr e with
  | BitVec.ofNat nExpr vExpr =>
    let n ← getNatValue? nExpr
    let v ← getNatValue? vExpr
    return ⟨n, BitVec.ofNat n v⟩
  | BitVec.ofNatLT nExpr vExpr _ =>
    let n ← getNatValue? nExpr
    let v ← getNatValue? vExpr
    return ⟨n, BitVec.ofNat n v⟩
  | _ =>
    let (v, type) ← getOfNatValue? e ``BitVec
    let n ← getNatValue? (← whnfD type.appArg!)
    return ⟨n, BitVec.ofNat n v⟩

/--
Returns the modulus of the wrapping numeric type `α` (`n` for `Fin n`, `2^w` for the
fixed-width types) if it is known. `USize`/`ISize` are not included: their widths are
platform-dependent.
-/
def getLitValueModulus? (α : Expr) : MetaM (Option Nat) := do
  match_expr α with
  | Fin n => getNatValue? n
  | BitVec w =>
    let some w ← getNatValue? w | return none
    return some (2 ^ w)
  | UInt8 => return some (2 ^ 8)
  | UInt16 => return some (2 ^ 16)
  | UInt32 => return some (2 ^ 32)
  | UInt64 => return some (2 ^ 64)
  | Int8 => return some (2 ^ 8)
  | Int16 => return some (2 ^ 16)
  | Int32 => return some (2 ^ 32)
  | Int64 => return some (2 ^ 64)
  | _ => return none

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

/--
Return `some i` if `e` is an `OfNat.ofNat`-application encoding `i` for a type with name `typeDeclName`,
or `Neg.neg`-application of one.
-/
private def getSignedOfNatValue? (e : Expr) (typeDeclName : Name) : MetaM (Option Int) := OptionT.run do
  match_expr e with
  | Neg.neg _ _ a =>
    let (n, _) ← getOfNatValue? a typeDeclName
    return -(n : Int)
  | _ =>
    let (n, _) ← getOfNatValue? e typeDeclName
    return n

/-- Return `some i` if `e` is an `OfNat.ofNat`-application encoding the `Int8` with value `i`, or `Neg.neg`-application of one. -/
def getInt8Value? (e : Expr) : MetaM (Option Int8) :=
  return (← getSignedOfNatValue? e ``Int8).map Int8.ofInt

/-- Return `some i` if `e` is an `OfNat.ofNat`-application encoding the `Int16` with value `i`, or `Neg.neg`-application of one. -/
def getInt16Value? (e : Expr) : MetaM (Option Int16) :=
  return (← getSignedOfNatValue? e ``Int16).map Int16.ofInt

/-- Return `some i` if `e` is an `OfNat.ofNat`-application encoding the `Int32` with value `i`, or `Neg.neg`-application of one. -/
def getInt32Value? (e : Expr) : MetaM (Option Int32) :=
  return (← getSignedOfNatValue? e ``Int32).map Int32.ofInt

/-- Return `some i` if `e` is an `OfNat.ofNat`-application encoding the `Int64` with value `i`, or `Neg.neg`-application of one. -/
def getInt64Value? (e : Expr) : MetaM (Option Int64) :=
  return (← getSignedOfNatValue? e ``Int64).map Int64.ofInt

/-- Recognize a non-negated `Float` literal: an `OfScientific` or `OfNat` application. -/
private def getFloatLit? (e : Expr) : MetaM (Option Float) := OptionT.run do
  match_expr e with
  | OfScientific.ofScientific type _ m s exp =>
    guard ((← whnfD type).isConstOf ``Float)
    let some s := getBoolLit? s | failure
    return Float.ofScientific (← getNatValue? m) s (← getNatValue? exp)
  | _ =>
    let (n, _) ← getOfNatValue? e ``Float
    return Float.ofNat n

/--
Return `some v` if `e` is a `Float` literal: an `OfScientific` or `OfNat` application, or `Neg.neg`
of either (e.g. `-1.5`).
-/
def getFloatValue? (e : Expr) : MetaM (Option Float) := do
  if let some v ← getFloatLit? e then return some v
  let_expr Neg.neg _ _ a ← e | return none
  let some v ← getFloatLit? a | return none
  return some (-v)

/-- Recognize a non-negated `Float32` literal: an `OfScientific` or `OfNat` application. -/
private def getFloat32Lit? (e : Expr) : MetaM (Option Float32) := OptionT.run do
  match_expr e with
  | OfScientific.ofScientific type _ m s exp =>
    guard ((← whnfD type).isConstOf ``Float32)
    let some s := getBoolLit? s | failure
    return Float32.ofScientific (← getNatValue? m) s (← getNatValue? exp)
  | _ =>
    let (n, _) ← getOfNatValue? e ``Float32
    return Float32.ofNat n

/--
Return `some v` if `e` is a `Float32` literal: an `OfScientific` or `OfNat` application, or `Neg.neg`
of either (e.g. `-1.5`).
-/
def getFloat32Value? (e : Expr) : MetaM (Option Float32) := do
  if let some v ← getFloat32Lit? e then return some v
  let_expr Neg.neg _ _ a ← e | return none
  let some v ← getFloat32Lit? a | return none
  return some (-v)

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
  if let some n ← getInt8Value? e then return toExpr n
  if let some n ← getInt16Value? e then return toExpr n
  if let some n ← getInt32Value? e then return toExpr n
  if let some n ← getInt64Value? e then return toExpr n
  -- `Float`/`Float32` literals are left untouched: there is no `ToExpr` instance for them, and their
  -- only canonical form would be `Float.ofBits`, which is less legible than the original literal.
  return e

private def isOfScientificLitArgs (m s exp : Expr) : MetaM Bool := do
  let s := s.consumeMData
  unless s.isConstOf ``Bool.true || s.isConstOf ``Bool.false do return false
  isNatValue m <&&> isNatValue exp

/-- Returns `true` if `OfScientific.ofScientific type _ m s exp` is a `Rat`, `Float`, or `Float32` literal. -/
private def isOfScientificLitValue (type m s exp : Expr) : MetaM Bool := do
  let type ← whnfD type
  unless type.isConstOf ``Rat || type.isConstOf ``Float || type.isConstOf ``Float32 do return false
  isOfScientificLitArgs m s exp

/-- Returns `true` if `OfNat.ofNat type n _` is a literal value. -/
private def isOfNatLitValue (type n : Expr) : MetaM Bool := do
  unless n.consumeMData.isRawNatLit do return false
  let type ← whnfD type
  let .const declName _ := type.getAppFn | return false
  if declName == ``Nat || declName == ``Int || declName == ``Rat || declName == ``Float || declName == ``Float32
      || declName == ``UInt8 || declName == ``UInt16 || declName == ``UInt32 || declName == ``UInt64
      || declName == ``Int8 || declName == ``Int16 || declName == ``Int32 || declName == ``Int64 then
    return true
  else if declName == ``Fin then
    isNonZeroNatValue (← whnfD type.appArg!)
  else if declName == ``BitVec then
    isNatValue (← whnfD type.appArg!)
  else
    return false

/--
Returns `true` if `Neg.neg _ _ a` is an `Int`, `Int8`, `Int16`, `Int32`, `Int64`, `Rat`, `Float`,
or `Float32` literal.
-/
private def isNegLitValue (a : Expr) : MetaM Bool := do
  match_expr a with
  | OfNat.ofNat type n _ =>
    unless n.consumeMData.isRawNatLit do return false
    let .const declName _ := (← whnfD type).getAppFn | return false
    return declName == ``Int || declName == ``Rat || declName == ``Float || declName == ``Float32
      || declName == ``Int8 || declName == ``Int16 || declName == ``Int32 || declName == ``Int64
  | OfScientific.ofScientific type _ m s exp => isOfScientificLitValue type m s exp
  | _ => return false

/-- Returns `true` if `HDiv.hDiv _ _ _ _ a b` encodes a rational literal. -/
private def isRatDivLitValue (a b : Expr) : MetaM Bool := do
  let a := match_expr a with
    | Neg.neg _ _ a => a
    | _ => a
  isRatOfNat a <&&> isRatOfNat b
where
  isRatOfNat (e : Expr) : MetaM Bool := do
    let_expr OfNat.ofNat type n _ := e | return false
    unless n.consumeMData.isRawNatLit do return false
    return (← whnfD type).getAppFn.isConstOf ``Rat

/--
Returns `true` if `e` is a literal value, i.e., one of the `get*Value?` functions above returns `some _`.
-/
def isLitValue (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  if let .lit (.strVal _) := e then return true
  if e.consumeMData.isRawNatLit then return true
  match_expr e with
  | OfNat.ofNat type n _ => isOfNatLitValue type n
  | Neg.neg _ _ a => isNegLitValue a
  | Char.ofNat n => isNatValue n
  | BitVec.ofNat w v => isNatValue w <&&> isNatValue v
  | BitVec.ofNatLT w v _ => isNatValue w <&&> isNatValue v
  | OfScientific.ofScientific type _ m s exp => isOfScientificLitValue type m s exp
  | HDiv.hDiv _ _ _ _ a b => isRatDivLitValue a b
  | _ => return false

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
      eagerReflBoolTrue
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
