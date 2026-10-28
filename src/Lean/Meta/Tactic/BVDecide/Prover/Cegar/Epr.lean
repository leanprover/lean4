/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Subsolver
import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Function
import Std.Tactic.BVDecide.EPR.BitVec
import Lean.Meta.Sym.InferType

/-!
This module contains the implementation of EPR handling via MBQI.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Tactic.BVDecide

namespace Cegar

namespace FunModel

-- TODO: projections
/--
Complete the model of an EPR relation, `predPattern` and return a lambda representing the completed model.
-/
def toLambda (model : FunModel) (predPattern : Expr) : Sym.SymM Expr := do
  lambdaTelescope predPattern fun args _ => do
    let ptr : Sym.ExprPtr := ⟨predPattern⟩
    -- Predicates that only occur below quantifiers have no entry yet.
    let entry := model.model[ptr]?.getD {}
    let condExpr := mkConst ``cond [1]
    let andExpr := mkConst ``Bool.and
    let returnType ← Sym.share <| toTypeExpr (BitVec 1)
    -- TODO: choose more cleverly
    let default := toExpr 0#1
    let mut func := default
    for (input, output) in entry.map do
      let mkEq (lhs rhs : Expr) : Sym.SymM Expr :=
        mkAppM ``BEq.beq #[lhs, rhs]
      let mut discr ← mkEq args[0]! (toExpr input[0]!.bv)
      for arg in args[1...*], ⟨val⟩ in input[1...*] do
        discr := mkApp2 andExpr (← mkEq arg (toExpr val)) discr
      func := mkApp4 condExpr returnType discr (toExpr output.fst.bv) func
    func ← mkLambdaFVars args func
    Sym.share func

end FunModel

structure EprCtx where
  cex : CegarM.CounterExample

structure EprState where
  completionCache : Std.HashMap Expr Expr := {}

abbrev EprM := SubsolverT <| ReaderT EprCtx StateRefT EprState CegarM

namespace EprM

def run (cex : CegarM.CounterExample) (x : EprM α) : CegarM α := do
  let ctx ← CegarM.getTacticContext
  let goal := (← read).goal
  StateRefT'.run' (ReaderT.run (SubsolverT.run ctx goal x) { cex }) {}

def mkInstConsts (hyp : EPR.QuantifiedFact) (hypIdx : Nat) : EprM (Array Expr) := do
  let mut consts := Array.emptyWithCapacity hyp.boundSorts.size
  let eprProblem := (← getThe BVDecide.State).theoryState.eprState.problem
  for h : quantIdx in 0...hyp.boundSorts.size do
    let sort := hyp.boundSorts[quantIdx]
    let sortInfo := eprProblem.sortInfo[sort]!
    let const ← Sym.share <| mkApp4 (mkConst ``EPR.BitVec.instConst [sortInfo.level]) sortInfo.type (toExpr hypIdx) (toExpr quantIdx) sortInfo.default
    consts := consts.push const
  return consts

def completedPred (pred : Expr) : EprM Expr := do
  if let some completed := (← getThe EprState).completionCache[pred]? then
    return completed
  else
    let completed ← fillCache pred
    modifyThe EprState fun s => { s with completionCache := s.completionCache.insert pred completed }
    return completed
where
  fillCache (pred : Expr) : EprM Expr := do
    let pattern ← eta pred
    let funModel := (← getThe CegarM.State).theoryState.funState.currentModel
    funModel.toLambda pattern

  eta (e : Expr) : Sym.SymM Expr := do
    let type ← Sym.inferType e
    Sym.share <| ← forallTelescope type fun args _ => mkLambdaFVars args (mkAppN pred args)


def substModel (e : Expr) : EprM TransformStep := do
  let model := (← read).cex
  if let some value := model.exprCex[e]? then
    return .done <| toExpr value.bv
  else
    e.withApp fun pred args => do
      let .const constName _ := pred | return .continue
      let some predArity := EPR.toBvPredArity[constName]? | return .continue
      let encodingArgsIdx := predArity * 4 + 1
      if args.size < encodingArgsIdx then return .continue
      let encodedPred ← Sym.share <| mkAppN pred args[0...encodingArgsIdx]
      let remainingArgs := args[encodingArgsIdx...*]
      let completedFun ← completedPred encodedPred
      return .done <| completedFun.beta remainingArgs


def mkCounterInst (hyp : EPR.QuantifiedFact) (quantCex : CegarM.CounterExample)
    (instConsts : Array Expr) : EprM Normalize.Hyp := do
  let eprProblem := (← getThe BVDecide.State).theoryState.eprState.problem
  let sortInfos := hyp.boundSorts.map (eprProblem.sortInfo[·]!)
  let mut assignment := #[]
  for instConst in instConsts, sortInfo in sortInfos do
    let atom := sortInfo.appToBv instConst
    let instConstVal := quantCex.exprCex[atom]!
    assignment := assignment.push <| ← recoverValue instConstVal sortInfo
  hyp.instantiate assignment
where
  -- TODO: potentially cache
  -- TODO: choose representative smarter
  recoverValue (value : BVExpr.PackedBitVec) (sortInfo : EPR.BvSortInfo) : EprM Expr := do
    for element in sortInfo.elements do
      let encodedElement := sortInfo.appToBv element
      let value' := (← read).cex.exprCex[encodedElement]!
      if value == value' then
        return element
    throwError m!"TODO: unreachable"


def checkQuant (hyp : EPR.QuantifiedFact) (hypIdx : Nat) : EprM Bool := do
  withTraceNode `Meta.Tactic.bv.epr (fun _ => return m!"MBQI check for {hyp.hyp.type}") do
  let instConsts ← mkInstConsts hyp hypIdx
  let inst := hyp.instantiateType instConsts
  let transformed ← Lean.Core.transform inst (pre := substModel)
  let negated ← Sym.shareCommon <| mkNot transformed
  SubsolverT.push #[{
    name := .anonymous
    type := negated
    value := ← mkSorry negated true
    source := .epr
  }]
  let res ← SubsolverT.check
  SubsolverT.pop
  match res with
  | .ok .. =>
    trace[Meta.Tactic.bv.epr] m!"Quantifier is consistent"
    return false
  | .error quantCex =>
    trace[Meta.Tactic.bv.epr] m!"Detected quantifier violation"
    let inst ← mkCounterInst hyp quantCex instConsts
    trace[Meta.Tactic.bv.epr] m!"New instance: {inst.type}"
    CegarM.pushNewHyp {
      hyp := inst
      tacticProof := throwError m!"Cannot squeeze EPR proofs TODO"
      grindProof := throwError m!"Cannot squeeze EPR proofs TODO"
    }
    return true

end EprM

def checkModel : EprM Bool := do
  let eprProblem := (← getThe BVDecide.State).theoryState.eprState.problem
  let mut added := false
  for h : idx in 0...eprProblem.quantifiedFacts.size do
    let quant := eprProblem.quantifiedFacts[idx]
    added := added || (← EprM.checkQuant quant idx)
  return added

public def checkEpr (cex : CegarM.CounterExample) : CegarM Bool :=
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"EPR MBQI") do
  unless (← CegarM.getTacticContext).config.epr do return false
  EprM.run cex do
    checkModel

end Cegar

end Lean.Meta.Tactic.BVDecide
