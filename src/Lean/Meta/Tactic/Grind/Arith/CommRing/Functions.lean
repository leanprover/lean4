/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
public section
namespace Lean.Meta.Grind.Arith.CommRing
variable [MonadLiftT MetaM m] [MonadError m] [Monad m] [MonadCanon m]

section
variable [MonadRing m]
def mkUnaryFn (type : Expr) (u : Level) (instDeclName : Name) (declName : Name) : m Expr := do
  let inst ← MonadCanon.synthInstance <| mkApp (mkConst instDeclName [u]) type
  canonExpr <| mkApp2 (mkConst declName [u]) type inst

def mkBinHomoFn (type : Expr) (u : Level) (instDeclName : Name) (declName : Name) : m Expr := do
  let inst ← MonadCanon.synthInstance <| mkApp3 (mkConst instDeclName [u, u, u]) type type type
  canonExpr <| mkApp4 (mkConst declName [u, u, u]) type type type inst

def mkPowFn (u : Level) (type : Expr) (semiringInst : Expr) : m Expr := do
  let inst ← MonadCanon.synthInstance <| mkApp3 (mkConst ``HPow [u, 0, u]) type Nat.mkType type
  let inst' := mkApp2 (mkConst ``Grind.Semiring.npow [u]) type semiringInst
  checkInst inst inst'
  canonExpr <| mkApp4 (mkConst ``HPow.hPow [u, 0, u]) type Nat.mkType type inst
where
  checkInst (inst inst' : Expr) : MetaM Unit := do
    unless (← isDefEqD inst inst') do
      throwError "instance for power operator{indentExpr inst}\nis not definitionally equal to the `Grind.Semiring` one{indentExpr inst'}"

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
  | some inst => checkInst inst inst'; pure inst
  canonExpr <| mkApp2 (mkConst ``NatCast.natCast [u]) type inst
where
  checkInst (inst inst' : Expr) : MetaM Unit := do
    unless (← isDefEqD inst inst') do
      throwError "instance for natCast{indentExpr inst}\nis not definitionally equal to the `Grind.Semiring` one{indentExpr inst'}"

variable [MonadLiftT MetaM m] [MonadError m] [Monad m] [MonadRing m]

def getAddFn : m Expr := do
  let ring ← getRing
  if let some addFn := ring.addFn? then return addFn
  let addFn ← mkBinHomoFn ring.type ring.u ``HAdd ``HAdd.hAdd
  modifyRing fun s => { s with addFn? := some addFn }
  return addFn

def getSubFn : m Expr := do
  let ring ← getRing
  if let some subFn := ring.subFn? then return subFn
  let subFn ← mkBinHomoFn ring.type ring.u ``HSub ``HSub.hSub
  modifyRing fun s => { s with subFn? := some subFn }
  return subFn

def getMulFn : m Expr := do
  let ring ← getRing
  if let some mulFn := ring.mulFn? then return mulFn
  let mulFn ← mkBinHomoFn ring.type ring.u ``HMul ``HMul.hMul
  modifyRing fun s => { s with mulFn? := some mulFn }
  return mulFn

def getNegFn : m Expr := do
  let ring ← getRing
  if let some negFn := ring.negFn? then return negFn
  let negFn ← mkUnaryFn ring.type ring.u ``Neg ``Neg.neg
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
    | some inst => checkInst inst inst'; pure inst
  let intCastFn ← canonExpr <| mkApp2 (mkConst ``IntCast.intCast [ring.u]) ring.type inst
  modifyRing fun s => { s with intCastFn? := some intCastFn }
  return intCastFn
where
  checkInst (inst inst' : Expr) : MetaM Unit := do
    unless (← isDefEqD inst inst') do
      throwError "instance for intCast{indentExpr inst}\nis not definitionally equal to the `Grind.Ring` one{indentExpr inst'}"

def getNatCastFn : m Expr := do
  let ring ← getRing
  if let some natCastFn := ring.natCastFn? then return natCastFn
  let natCastFn ← mkNatCastFn ring.u ring.type ring.semiringInst
  modifyRing fun s => { s with natCastFn? := some natCastFn }
  return natCastFn

private def mkOne (u : Level) (type : Expr) (semiringInst : Expr) : m Expr := do
  let n := mkRawNatLit 1
  let ofNatInst := mkApp3 (mkConst ``Grind.Semiring.ofNat [u]) type semiringInst n
  canonExpr <| mkApp3 (mkConst ``OfNat.ofNat [u]) type n ofNatInst

def getOne [MonadLiftT GoalM m] : m Expr := do
  let ring ← getRing
  if let some one := ring.one? then return one
  let one ← mkOne ring.u ring.type ring.semiringInst
  modifyRing fun s => { s with one? := some one }
  internalize one 0
  return one
end

section
variable [MonadCommRing m]

def getInvFn : m Expr := do
  let ring ← getCommRing
  if ring.fieldInst?.isNone then
    throwError "`grind` internal error, type is not a field{indentExpr ring.type}"
  if let some invFn := ring.invFn? then return invFn
  let invFn ← mkUnaryFn ring.type ring.u ``Inv ``Inv.inv
  modifyCommRing fun s => { s with invFn? := some invFn }
  return invFn

end

end Lean.Meta.Grind.Arith.CommRing
