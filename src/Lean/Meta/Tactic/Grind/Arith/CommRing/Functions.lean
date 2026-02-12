/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
public import Lean.Meta.Sym.Arith.Ring.Functions
public section
namespace Lean.Meta.Grind.Arith.CommRing
export Sym.Arith.Ring (checkInst mkUnaryFn mkBinHomoFn mkPowFn mkNatCastFn
  getAddFn getSubFn getMulFn getNegFn getPowFn getIntCastFn getNatCastFn mkOne)

variable [MonadLiftT MetaM m] [MonadError m] [Monad m] [MonadCanon m]

section
variable [MonadRing m]

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
  let some fieldInst := ring.fieldInst?
    | throwError "`grind` internal error, type is not a field{indentExpr ring.type}"
  if let some invFn := ring.invFn? then return invFn
  let expectedInst := mkApp2 (mkConst ``Grind.Field.toInv [ring.u]) ring.type fieldInst
  let invFn ← mkUnaryFn ring.type ring.u ``Inv ``Inv.inv expectedInst
  modifyCommRing fun s => { s with invFn? := some invFn }
  return invFn
end

end Lean.Meta.Grind.Arith.CommRing
