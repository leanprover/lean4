/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
import Lean.Meta.Tactic.Grind.Simp
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

def getTermNatStructId? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToNatStructId.find? { expr := e }

/-- Returns `some natStructId` if `a` and `b` are elements of the same `NatModule` structure. -/
def inSameNatStruct? (a b : Expr) : GoalM (Option Nat) := do
  let some id ← getTermNatStructId? a | return none
  let some id' ← getTermNatStructId? b | return none
  unless id == id' do return none -- This can happen when we have heterogeneous equalities
  return id

def setTermNatStructId (e : Expr) : OfNatModuleM Unit := do
  let id ← getNatStructId
  if let some id' ← getTermNatStructId? e then
    unless id' == id do
      reportIssue! "expression in two different nat module structures in linarith module{indentExpr e}"
    return ()
  modify' fun s => { s with exprToNatStructId := s.exprToNatStructId.insert { expr := e } id }

private def mkOfNatModuleVar (e : Expr) : OfNatModuleM (Expr × Expr) := do
  if let some r := (← getNatStruct).termMap.find? { expr := e } then
    return r
  else
    let s ← getNatStruct
    let toQe ← shareCommon (mkApp s.toQFn e)
    let h    := mkApp s.rfl_q toQe
    let r := (toQe, h)
    modifyNatStruct fun s => { s with termMap := s.termMap.insert { expr := e } r }
    setTermNatStructId e
    markAsLinarithTerm e
    return r

private def isAddInst (natStruct : NatStruct) (inst : Expr) : Bool :=
  isSameExpr natStruct.addFn.appArg! inst
private def isZeroInst (natStruct : NatStruct) (inst : Expr) : Bool :=
  isSameExpr natStruct.zero.appArg! inst
private def isSMulInst (natStruct : NatStruct) (inst : Expr) : Bool :=
  isSameExpr natStruct.smulFn.appArg! inst

private partial def ofNatModule' (e : Expr) : OfNatModuleM (Expr × Expr) := do
  let s ← getStruct
  let ns ← getNatStruct
  match_expr e with
  | HAdd.hAdd _ _ _ i a b =>
    if isAddInst ns i then
      let (a', ha) ← ofNatModule' a
      let (b', hb) ← ofNatModule' b
      let e' := mkApp2 s.addFn a' b'
      let h := mkApp8 (mkConst ``Grind.IntModule.OfNatModule.add_congr [ns.u]) ns.type ns.natModuleInst a b a' b' ha hb
      pure (e', h)
    else
      mkOfNatModuleVar e
  | HSMul.hSMul _ _ _ i a b =>
    if isSMulInst ns i then
      let (b', hb) ← ofNatModule' b
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

def ofNatModule (e : Expr) : OfNatModuleM (Expr × Expr) := do
  if let some r := (← getNatStruct).termMap.find? { expr := e } then
    return r
  else
    let (e', h) ← ofNatModule' e
    let r ← preprocess e'
    let (e', h) ← if let some proof := r.proof? then
      pure (r.expr, (← mkEqTrans h proof))
    else
      pure (r.expr, h)
    setTermNatStructId e
    modifyNatStruct fun s => { s with termMap := s.termMap.insert { expr := e } (e', h) }
    return (e', h)

end Lean.Meta.Grind.Arith.Linear
