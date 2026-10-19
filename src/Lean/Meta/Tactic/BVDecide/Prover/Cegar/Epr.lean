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
import Lean.Meta.Tactic.BVDecide.Normalize.Rewrite
import Std.Tactic.BVDecide.EPR.BitVec
import Std.Tactic.BVDecide.Bitblast.Substitute

/-!
This module contains the implementation of EPR handling via MBQI.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Tactic.BVDecide

namespace Cegar

namespace FunModel

-- TODO: projections
-- TODO: potentially constant fold in here
/--
Complete the model of the EPR predicate `atom.pattern` to a total function.
-/
def completion (model : FunModel) (atom : EprTemplate.PredAtom) : BVLogicalExpr := Id.run do
  -- Predicates that only occur below quantifiers have no entry yet.
  let entry := model.model[(⟨atom.pattern⟩ : Sym.ExprPtr)]?.getD {}
  let mut zeroCount := 0
  let mut oneCount := 0
  for (_, (output, _)) in entry.map do
    if output.bv.toNat == 0 then
      zeroCount := zeroCount + 1
    else if output.bv.toNat == 1 then
      oneCount := oneCount + 1

  let defaultValue := if zeroCount ≤ oneCount then true else false
  let mut negatedConj : Option BVLogicalExpr := none
  for (input, (output, _)) in entry.map do
    if (output.bv.toNat == 1) == defaultValue then continue
    let mut inputDiscr : Option BVLogicalExpr := none
    for ⟨w, arg⟩ in atom.args, val in input do
      if h : val.w = w then
        let argEq := .literal <| .eq arg (.const (h ▸ val.bv))
        inputDiscr := some <|
          match inputDiscr with
          | none => argEq
          | some discr => .and discr argEq
      else
        unreachable!
    let negated := .not (inputDiscr.getD (.const true))
    negatedConj := some <|
      match negatedConj with
      | none => negated
      | some conj => .and conj negated

  match negatedConj with
  | none => return .const defaultValue
  | some conj => return if defaultValue then conj else .not conj

end FunModel

structure EprCtx where
  cex : CegarM.CounterExample

structure EprState where
  /--
  Here we record quantifiers and arguments we want to instantiate them with.
  We do not instantiate right away because the SymM state of the model check will be re-rolled
  later. This allows us to drop the expressions register in the sharing caches during the model
  check which we know to:
  1. Usually be different in the next model check because we substitute a different model
  2. Not be used again after the model check
  -/
  instances : Array (EPR.QuantifiedFact × Array Expr) := #[]

abbrev EprM := SubsolverT <| ReaderT EprCtx StateRefT EprState CegarM

def mkInstConsts (hyp : EPR.QuantifiedFact) : CegarM (Array Expr) := do
  let mut consts := Array.emptyWithCapacity hyp.boundSorts.size
  let eprProblem := (← getThe BVDecide.State).theoryState.eprState.problem
  for h : quantIdx in 0...hyp.boundSorts.size do
    let sort := hyp.boundSorts[quantIdx]
    let sortInfo := eprProblem.sortInfo[sort]!
    /-
    This construction means we share instConsts across multiple quantifiers, e.g. in
    ```
    h1 : ∀ (x y : α), guard x y → body x y
    h2 : ∀ (x : α), guard x → body x
    ```
    Both `x` will be represented by the same `instConst`. This allows us to share at least the sort
    membership guard condition on `x` and potentially parts of the body, should they overlap.
    -/
    let const ← Sym.share <| mkApp3 (mkConst ``EPR.BitVec.instConst [sortInfo.level]) sortInfo.type (toExpr quantIdx) sortInfo.default
    consts := consts.push const
  return consts

namespace EprTemplate

def collectPredAtoms : ReifyM (Std.HashMap Nat EprTemplate.PredAtom) := do
  let funState := (← get).theoryState.funState
  let mut predAtoms := {}
  for funAtom in funState.atoms, mask in funState.masks, pattern in funState.patterns do
    unless funAtom.isBoolAtom do continue
    let some atomNumber ← ReifyM.getAtomNumber (← funAtom.atomExpr) | continue
    let (some args, lemmas) ← LemmaM.run (reifyArgs funAtom.funExpr.getAppArgs mask) | continue
    unless lemmas.isEmpty do continue
    predAtoms := predAtoms.insert atomNumber { pattern, args }
  return predAtoms
where
  reifyArgs (args : Array Expr) (mask : Array Bool) :
      LemmaM (Option (Array ((w : Nat) × BVExpr w))) := do
    let mut reified := #[]
    for arg in args, m in mask do
      unless m do continue
      let some arg ← ReifiedBVExpr.of arg | return none
      reified := reified.push ⟨arg.width, arg.bvExpr⟩
    return some reified

/--
Instantiate each quantified fact with `instConsts` and reify its guards together with its negated
body.
-/
def build : CegarM EprTemplate :=
  withTraceNode `Meta.Tactic.bv.epr (fun _ => return m!"Reifying quantified facts") do
  let ctx ← CegarM.getTacticContext
  let goal := (← read).goal
  let eprProblem := (← getThe BVDecide.State).theoryState.eprState.problem
  SubsolverT.run ctx goal (trackFunAtoms := true) do
    let mut quants := Array.emptyWithCapacity eprProblem.quantifiedFacts.size
    for fact in eprProblem.quantifiedFacts do
      let instConsts ← mkInstConsts fact
      let (guards, body) := fact.instantiateParts instConsts
      let some (ty@(.const ``Bool []), lhs, rhs@(.const ``Bool.true [])) := body.eq? | unreachable!
      let negatedBody := mkApp3 (mkConst ``Eq [1]) ty (mkApp (mkConst ``Bool.not) lhs) rhs
      let hyps ← (guards.push negatedBody).mapM fun type => do
        let type ← Sym.shareCommon type
        return ({
          name := .anonymous
          type
          value := ← mkSorry type true
          source := .epr
        } : Normalize.Hyp)
      let exprs ← SubsolverT.reifyNormalized hyps
      quants := quants.push { fact, instConsts, exprs }
    let predAtoms ← SubsolverT.liftReifyM collectPredAtoms
    return { reifyState := ← SubsolverT.getReifyState, quants, predAtoms }

structure Substitution where
  template : EprTemplate
  cex : CegarM.CounterExample
  funModel : FunModel

def atomExpr? (template : EprTemplate) (idx : Nat) : Option Expr := do
  -- `build` fills this cache through `SubsolverT.getReifyState`.
  let (_, expr, _) ← (← template.reifyState.atomsAssignmentMapCache)[idx]?
  return expr

instance : AtomSubstitution Substitution where
  bvAtom subst w idx := do
    let value ← subst.cex.exprCex[← subst.template.atomExpr? idx]?
    if h : value.w = w then some (.const (h ▸ value.bv)) else none
  boolAtom s idx := do
    let atom ← s.template.predAtoms[idx]?
    let expr ← s.template.atomExpr? idx
    /-
    We only bother computing the completion if this particular model doesn't have a concrete value
    for this predicate application already.
    -/
    guard <| !s.cex.exprCex.contains expr
    return s.funModel.completion atom

end EprTemplate

/--
We pre-process and reify all quantifiers once, then substitute the models in on the reified
expression level during MBQI checks.
-/
def getEprTemplate : CegarM EprTemplate := do
  if let some template := (← CegarM.getTheoryState).eprTemplate then
    return template
  let template ← EprTemplate.build
  CegarM.modifyTheoryState fun s => { s with eprTemplate := some template }
  return template

namespace EprM

def run (template : EprTemplate) (cex : CegarM.CounterExample) (x : EprM α) :
    CegarM (α × EprState) := do
  let ctx ← CegarM.getTacticContext
  let goal := (← read).goal
  let x := SubsolverT.run ctx goal x (reifyState := template.reifyState)
  StateRefT'.run (ReaderT.run x { cex }) {}

def recordInstance (hyp : EPR.QuantifiedFact) (args : Array Expr) : EprM Unit := do
  modifyThe EprState fun s => { s with instances := s.instances.push (hyp, args) }

def recordCounterInst (hyp : EPR.QuantifiedFact) (quantCex : CegarM.CounterExample)
    (instConsts : Array Expr) : EprM Unit := do
  let eprProblem := (← getThe BVDecide.State).theoryState.eprState.problem
  let sortInfos := hyp.boundSorts.map (eprProblem.sortInfo[·]!)
  let mut assignment := #[]
  for instConst in instConsts, sortInfo in sortInfos do
    let atom := sortInfo.appToBv instConst
    let instConstVal := quantCex.exprCex[atom]!
    assignment := assignment.push <| ← recoverValue instConstVal sortInfo
  withTraceNode `Meta.Tactic.bv.epr (fun _ => return m!"New instance with: {assignment}") do
    recordInstance hyp assignment
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

/--
Check whether the model violates `quant`, given the expressions of `quant` with the model
substituted.
-/
def checkQuant (quant : EprTemplate.Quant) (exprs : Array BVLogicalExpr) : EprM Unit := do
  withTraceNode `Meta.Tactic.bv.epr (fun _ => return m!"MBQI check for {quant.fact.hyp.type}") do
  let exprs := exprs.filter (· != .const true)
  if exprs.contains (.const false) then
    trace[Meta.Tactic.bv.epr] m!"Quantifier is consistent"
    return
  let res ← withTraceNode `Meta.Tactic.bv.epr (fun _ => return m!"Running consistency check") do
    SubsolverT.pushReified exprs
    let res ← SubsolverT.check
    SubsolverT.pop
    return res
  match res with
  | .ok .. =>
    trace[Meta.Tactic.bv.epr] m!"Quantifier is consistent"
  | .error quantCex =>
    trace[Meta.Tactic.bv.epr] m!"Detected quantifier violation"
    recordCounterInst quant.fact quantCex quant.instConsts

end EprM

def checkModel (template : EprTemplate) : EprM Unit := do
  let funModel := (← getThe CegarM.State).theoryState.funState.currentModel
  let subst : EprTemplate.Substitution := { template, cex := (← read).cex, funModel }
  let exprs := BVLogicalExpr.substituteAll subst (template.quants.flatMap (·.exprs))
  let mut offset := 0
  for quant in template.quants do
    let next := offset + quant.exprs.size
    EprM.checkQuant quant exprs[offset...next].toArray
    offset := next

/--
Instantiate `hyp` with sort elements. As these elements satisfy their guards by construction we
simplify each guard to `True` on its own to derive the body directly.
-/
def instantiateWithoutGuards (hyp : EPR.QuantifiedFact) (args : Array Expr) :
    CegarM Normalize.Hyp := do
  let (guards, body) := hyp.instantiateParts args
  let proofs ← CegarM.liftPreProcessM do
    Normalize.withRewriteRules fun _ _ simpMethods simpConfig => do
      guards.mapM fun guard => do
        let guard ← Sym.shareCommon guard
        match ← Normalize.PreProcessM.simpExpr .rewrite simpMethods simpConfig guard with
        | .step (.const ``True []) proof .. =>
          return mkApp2 (mkConst ``of_eq_true) guard proof
        | _ => throwError "unreachable TODO"
  return {
    name := hyp.hyp.name ++ `inst
    type := ← Sym.shareCommon body
    value := mkAppN hyp.hyp.value (args ++ proofs)
    source := hyp.hyp.source
  }

public def checkEpr (cex : CegarM.CounterExample) : CegarM Bool :=
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"EPR MBQI") do
  unless (← CegarM.getTacticContext).config.epr do return false
  let template ← getEprTemplate
  let (_, s) ← EprM.run template cex do
    checkModel template
  for (hyp, args) in s.instances do
    let inst ← instantiateWithoutGuards hyp args
    trace[Meta.Tactic.bv.epr] m!"Instance: {inst}"
    CegarM.pushNewHyp {
      hyp := inst
      tacticProof := throwError m!"Cannot squeeze EPR proofs TODO"
      grindProof := throwError m!"Cannot squeeze EPR proofs TODO"
      isNormalized := true -- TODO: contemplate
    }
  return !s.instances.isEmpty

end Cegar

end Lean.Meta.Tactic.BVDecide
