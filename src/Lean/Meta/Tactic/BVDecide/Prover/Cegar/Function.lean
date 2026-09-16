/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
import Lean.Meta.Sym.InferType

/-!
TODO
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Tactic.BVDecide

namespace Cegar

deriving instance Inhabited, BEq, Hashable for Sum

structure FunModel.Entry where
  -- TODO: bzla caches hashes of `Array BVExpr.PackedBitVec` here
  map : Std.HashMap (Array (BVExpr.PackedBitVec ⊕ Expr)) (BVExpr.PackedBitVec × Expr)
  deriving Inhabited

structure FunModel where
  model : Std.HashMap Sym.ExprPtr FunModel.Entry := {}
  deriving Inhabited

namespace FunModel

namespace Entry

def new (args : Array (BVExpr.PackedBitVec ⊕ Expr)) (value : BVExpr.PackedBitVec) (atom : Expr) : Entry :=
  {
    map := {(args, (value, atom))}
  }

def insert (entry : Entry) (args : Array (BVExpr.PackedBitVec ⊕ Expr)) (value : BVExpr.PackedBitVec)
    (atom : Expr) : Entry :=
  { entry with
      map := entry.map.insert args (value, atom)
  }

end Entry

def findConflictWith? (funModel : FunModel) (fn : Expr) (args : Array (BVExpr.PackedBitVec ⊕ Expr))
    (value : BVExpr.PackedBitVec) : Option Expr := do
  let key : Sym.ExprPtr := { expr := fn }
  let entry ← funModel.model[key]?
  let (value', atom') ← entry.map[args]?
  if value ≠ value' then
    return atom'
  else
    none

def insert (funModel : FunModel) (fn : Expr) (args : Array (BVExpr.PackedBitVec ⊕ Expr))
    (value : BVExpr.PackedBitVec) (atom : Expr) : FunModel :=
  { funModel with
      model := funModel.model.alter ⟨fn⟩
        fun
          | some entry => some <| entry.insert args value atom
          | none => some <| Entry.new args value atom
  }

end FunModel

def addFunctionCongruenceLemma (lhs rhs : Expr) (mask : Array Bool) (pattern : Expr) :
    CegarM Unit := do
  let lhsArgs := lhs.getAppArgs
  let rhsArgs := rhs.getAppArgs
  let mut congrLemma ← getCongrLemmaForPattern pattern
  for lhsArg in lhsArgs, rhsArg in rhsArgs, m in mask do
    unless m do continue
    congrLemma := mkApp2 congrLemma lhsArg rhsArg
  congrLemma ← Sym.share congrLemma
  let congrStatement ← Sym.inferType congrLemma
  trace[Meta.Tactic.bv] m!"{congrStatement}"
  CegarM.pushNewHyp {
    name := `congr
    type := congrStatement
    value := congrLemma
    source := .cegar
  }
  CegarM.setDidChange true
where
  getCongrLemmaForPattern (pattern : Expr) : CegarM Expr := do
    let key : Sym.ExprPtr := { expr := pattern }
    if let some lem := (← CegarM.getTheoryState).funState.congrCache[key]? then
      return lem
    else
      let lem ← mkCongrLemmaForPattern pattern
      CegarM.modifyTheoryState fun ts =>
        { ts with funState.congrCache := ts.funState.congrCache.insert key lem}
      return lem

  mkCongrLemmaForPattern (pattern : Expr) : CegarM Expr := do
    lambdaTelescope pattern fun lhsArgs _ => do
    lambdaTelescope pattern fun rhsArgs _ => do
      let mut equalityDecls := #[]
      for lhsArg in lhsArgs, rhsArg in rhsArgs do
        equalityDecls := equalityDecls.push (.anonymous, ← mkEq lhsArg rhsArg)
      withLocalDeclsDND equalityDecls fun equalities => do
        let mut lem ← mkAppM ``congrArg #[pattern, equalities[0]!]
        for equality in equalities[1...*] do
          lem ← mkAppM ``congr #[lem, equality]
        let mut fvars := #[]
        for lhsArg in lhsArgs, rhsArg in rhsArgs do
          fvars := fvars.push lhsArg |>.push rhsArg
        fvars := fvars ++ equalities
        mkLambdaFVars fvars lem

open Std.Tactic.BVDecide.EfficientEval in
public def checkUf (cex : CegarM.CounterExample) : CegarM Bool :=
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"UF conflict detection") do
  unless (← CegarM.getTacticContext).config.uf do return false
  let funState := (← getThe BVDecide.State).theoryState.funState
  let mut funModel : FunModel := {}
  for funAtom in funState.atoms, mask in funState.masks, funPattern in funState.patterns do
    let args ← evalArgs funAtom.getAppArgs mask
    let value := cex.exprCex[funAtom]!
    trace[Meta.Tactic.bv] m!"Checking: {funAtom}, value: {value.bv}, pattern: {funPattern}"
    if let some conflict := funModel.findConflictWith? funPattern args value then
      assert! funAtom != conflict
      trace[Meta.Tactic.bv] m!"Detected UF conflict on: {funAtom} vs {conflict}"
      addFunctionCongruenceLemma funAtom conflict mask funPattern
    else
      funModel := funModel.insert funPattern args value funAtom
  return ← CegarM.getDidChange
where
  evalArgs (args : Array Expr) (mask : Array Bool) : CegarM (Array (BVExpr.PackedBitVec ⊕ Expr)) := do
    args.mapIdxM fun idx arg => do
      if mask[idx]! then
        if (← isValidBitVecAtom arg).isSome then
          let some reified ← ReifiedBVExpr.of arg | unreachable!
          let res := BVExpr.evalEfficient (cex.atomCex.getD · ⟨0#1⟩) reified.bvExpr
          return .inl ⟨res⟩
        else if ← isValidBoolAtom arg then
          let some reified ← ReifiedBVLogical.of arg | unreachable!
          let res := BVLogicalExpr.evalEfficient (cex.atomCex.getD · ⟨0#1⟩) reified.bvExpr
          return .inl ⟨BitVec.ofBool res⟩
        else
          unreachable!
      else
        return .inr arg

end Cegar

end Lean.Meta.Tactic.BVDecide
