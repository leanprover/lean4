/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.Ring.MonadRing
public import Lean.Meta.Basic
public section
namespace Lean.Meta.Sym.Arith.Ring
variable [MonadLiftT MetaM m] [MonadError m] [Monad m] [MonadCanon m]

section
variable [MonadRing m]

def checkInst (declName : Name) (inst inst' : Expr) : MetaM Unit := do
  unless (← isDefEqI inst inst') do
    throwError "error while initializing `grind ring` operators:\ninstance for `{declName}` {indentExpr inst}\nis not definitionally equal to the expected one {indentExpr inst'}\nwhen only reducible definitions and instances are reduced"

def mkUnaryFn (type : Expr) (u : Level) (instDeclName : Name) (declName : Name) (expectedInst : Expr) : m Expr := do
  let inst ← MonadCanon.synthInstance <| mkApp (mkConst instDeclName [u]) type
  checkInst declName inst expectedInst
  canonExpr <| mkApp2 (mkConst declName [u]) type inst

def mkBinHomoFn (type : Expr) (u : Level) (instDeclName : Name) (declName : Name) (expectedInst : Expr) : m Expr := do
  let inst ← MonadCanon.synthInstance <| mkApp3 (mkConst instDeclName [u, u, u]) type type type
  checkInst declName inst expectedInst
  canonExpr <| mkApp4 (mkConst declName [u, u, u]) type type type inst

def mkPowFn (u : Level) (type : Expr) (semiringInst : Expr) : m Expr := do
  let inst ← MonadCanon.synthInstance <| mkApp3 (mkConst ``HPow [u, 0, u]) type Nat.mkType type
  let inst' := mkApp2 (mkConst ``Grind.Semiring.npow [u]) type semiringInst
  checkInst ``HPow.hPow inst inst'
  canonExpr <| mkApp4 (mkConst ``HPow.hPow [u, 0, u]) type Nat.mkType type inst

def mkNatCastFn (u : Level) (type : Expr) (semiringInst : Expr) : m Expr := do
  let inst' := mkApp2 (mkConst ``Grind.Semiring.natCast [u]) type semiringInst
  let instType := mkApp (mkConst ``NatCast [u]) type
  -- Note that `Semiring.natCast` is not registered as a global instance
  -- (to avoid introducing unwanted coercions)
  -- so merely having a `Semiring α` instance
  -- does not guarantee that an `NatCast α` will be available.
  -- When both are present we verify that they are defeq,
  -- and otherwise fall back to the field of the `Semiring α` instance that we already have.
  let inst ← match (← MonadCanon.synthInstance? instType) with
  | none => pure inst'
  | some inst => checkInst ``NatCast.natCast inst inst'; pure inst
  canonExpr <| mkApp2 (mkConst ``NatCast.natCast [u]) type inst

def getAddFn : m Expr := do
  let ring ← getRing
  if let some addFn := ring.addFn? then return addFn
  let expectedInst := mkApp2 (mkConst ``instHAdd [ring.u]) ring.type <| mkApp2 (mkConst ``Grind.Semiring.toAdd [ring.u]) ring.type ring.semiringInst
  let addFn ← mkBinHomoFn ring.type ring.u ``HAdd ``HAdd.hAdd expectedInst
  modifyRing fun s => { s with addFn? := some addFn }
  return addFn

def getSubFn : m Expr := do
  let ring ← getRing
  if let some subFn := ring.subFn? then return subFn
  let expectedInst := mkApp2 (mkConst ``instHSub [ring.u]) ring.type <| mkApp2 (mkConst ``Grind.Ring.toSub [ring.u]) ring.type ring.ringInst
  let subFn ← mkBinHomoFn ring.type ring.u ``HSub ``HSub.hSub expectedInst
  modifyRing fun s => { s with subFn? := some subFn }
  return subFn

def getMulFn : m Expr := do
  let ring ← getRing
  if let some mulFn := ring.mulFn? then return mulFn
  let expectedInst := mkApp2 (mkConst ``instHMul [ring.u]) ring.type <| mkApp2 (mkConst ``Grind.Semiring.toMul [ring.u]) ring.type ring.semiringInst
  let mulFn ← mkBinHomoFn ring.type ring.u ``HMul ``HMul.hMul expectedInst
  modifyRing fun s => { s with mulFn? := some mulFn }
  return mulFn

def getNegFn : m Expr := do
  let ring ← getRing
  if let some negFn := ring.negFn? then return negFn
  let expectedInst := mkApp2 (mkConst ``Grind.Ring.toNeg [ring.u]) ring.type ring.ringInst
  let negFn ← mkUnaryFn ring.type ring.u ``Neg ``Neg.neg expectedInst
  modifyRing fun s => { s with negFn? := some negFn }
  return negFn

def getPowFn : m Expr := do
  let ring ← getRing
  if let some powFn := ring.powFn? then return powFn
  let powFn ← mkPowFn ring.u ring.type ring.semiringInst
  modifyRing fun s => { s with powFn? := some powFn }
  return powFn

def getIntCastFn : m Expr := do
  let ring ← getRing
  if let some intCastFn := ring.intCastFn? then return intCastFn
  let inst' := mkApp2 (mkConst ``Grind.Ring.intCast [ring.u]) ring.type ring.ringInst
  let instType := mkApp (mkConst ``IntCast [ring.u]) ring.type
  -- Note that `Ring.intCast` is not registered as a global instance
  -- (to avoid introducing unwanted coercions)
  -- so merely having a `Ring α` instance
  -- does not guarantee that an `IntCast α` will be available.
  -- When both are present we verify that they are defeq,
  -- and otherwise fall back to the field of the `Ring α` instance that we already have.
  let inst ← match (← MonadCanon.synthInstance? instType) with
    | none => pure inst'
    | some inst => checkInst ``Int.cast inst inst'; pure inst
  let intCastFn ← canonExpr <| mkApp2 (mkConst ``IntCast.intCast [ring.u]) ring.type inst
  modifyRing fun s => { s with intCastFn? := some intCastFn }
  return intCastFn

def getNatCastFn : m Expr := do
  let ring ← getRing
  if let some natCastFn := ring.natCastFn? then return natCastFn
  let natCastFn ← mkNatCastFn ring.u ring.type ring.semiringInst
  modifyRing fun s => { s with natCastFn? := some natCastFn }
  return natCastFn

def mkOne (u : Level) (type : Expr) (semiringInst : Expr) : m Expr := do
  let n := mkRawNatLit 1
  let ofNatInst := mkApp3 (mkConst ``Grind.Semiring.ofNat [u]) type semiringInst n
  canonExpr <| mkApp3 (mkConst ``OfNat.ofNat [u]) type n ofNatInst

end

end Lean.Meta.Sym.Arith.Ring
