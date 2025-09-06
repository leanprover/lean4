/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
import Init.Grind.Module.OfNatModule
public section
namespace Lean.Meta.Grind.Arith.Linear

structure OfNatModuleM.Context where
  natStructId : Nat

abbrev OfNatModuleM := ReaderT OfNatModuleM.Context GoalM

abbrev OfNatModuleM.run (natStructId : Nat) (x : OfNatModuleM α) : GoalM α :=
  x { natStructId }

abbrev getNatStructId : OfNatModuleM Nat :=
  return (← read).natStructId

def getNatStruct : OfNatModuleM NatStruct := do
  let s ← get'
  let natStructId ← getNatStructId
  if h : natStructId < s.natStructs.size then
    return s.natStructs[natStructId]
  else
    throwError "`grind` internal error, invalid natStructId"

protected def OfNatModuleM.getStruct : OfNatModuleM Struct := do
  let ns ← getNatStruct
  LinearM.run ns.structId getStruct

instance : MonadGetStruct OfNatModuleM where
  getStruct := OfNatModuleM.getStruct

@[inline] def modifyNatStruct (f : NatStruct → NatStruct) : OfNatModuleM Unit := do
  let id ← getNatStructId
  modify' fun s => { s with natStructs := s.natStructs.modify id f }

private def mkOfNatModuleVar (e : Expr) : OfNatModuleM (Expr × Expr) := do
  let s ← getNatStruct
  let toQe := mkApp s.toQFn e
  let h    := mkApp s.rfl toQe
  markAsLinarithTerm e
  return (toQe, h)

private def isAddInst (natStruct : NatStruct) (inst : Expr) : Bool :=
  isSameExpr natStruct.addFn.appArg! inst
private def isZeroInst (natStruct : NatStruct) (inst : Expr) : Bool :=
  isSameExpr natStruct.zero.appArg! inst
def isSMulInst (natStruct : NatStruct) (inst : Expr) : Bool :=
  isSameExpr natStruct.smulFn.appArg! inst

partial def ofNatModule (e : Expr) : OfNatModuleM (Expr × Expr) := do
  if let some r := (← getNatStruct).termMap.find? { expr := e } then
    return r
  else
    let s ← getStruct
    let ns ← getNatStruct
    let r ← match_expr e with
      | HAdd.hAdd _ _ _ i a b =>
        if isAddInst ns i then
          let (a', ha) ← ofNatModule a
          let (b', hb) ← ofNatModule b
          let e' := mkApp2 s.addFn a' b'
          let h := mkApp8 (mkConst ``Grind.IntModule.OfNatModule.add_congr [ns.u]) ns.type ns.natModuleInst a b a' b' ha hb
          pure (e', h)
        else
          mkOfNatModuleVar e
      | HSMul.hSMul _ _ _ i a b =>
        if isSMulInst ns i then
          let (b', hb) ← ofNatModule b
          let e' := mkApp2 s.nsmulFn a b'
          let h := mkApp6 (mkConst ``Grind.IntModule.OfNatModule.smul_congr [ns.u]) ns.type ns.natModuleInst a b b' hb
          pure (e', h)
        else
          mkOfNatModuleVar e
      | Zero.zero _ i =>
        if isZeroInst ns i then
          let e' := s.zero
          let h := mkApp2 (mkConst ``Grind.IntModule.OfNatModule.toQ_zero [ns.u]) ns.type ns.natModuleInst
          pure (e', h)
        else
          mkOfNatModuleVar e
      | _ => mkOfNatModuleVar e
    modifyNatStruct fun s => { s with termMap := s.termMap.insert { expr := e } r }
    return r

end Lean.Meta.Grind.Arith.Linear
