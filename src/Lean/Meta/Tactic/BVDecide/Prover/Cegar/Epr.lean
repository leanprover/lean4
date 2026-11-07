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
import Lean.Meta.Tactic.BVDecide.EPR.InstSets

/-!
This module contains the implementation of EPR handling via MBQI.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Tactic.BVDecide

namespace Cegar

/--
A Z3 style projection of a predicate argument onto the values of its instantiation set. Values in
`values` are mapped to themselves, all other values are mapped to `elseValue`, which is in `values`.
-/
structure Projection where
  /--
  All values of the inst set for the predicate application position this projection applies to.
  -/
  values : Array BVExpr.PackedBitVec
  /--
  The default value chosen by the projection if the input is not in `values`.
  -/
  elseValue : BVExpr.PackedBitVec

def mkEqConst (atom : (w : Nat) × BVExpr w) (val : BVExpr.PackedBitVec) : BVLogicalExpr :=
  if h : val.w = atom.1 then .literal (.eq atom.2 (.const (h ▸ val.bv))) else unreachable!

namespace FunModel

-- TODO: potentially constant fold in here
def completion (model : FunModel) (pred : EprTemplate.PredAtom) (proj : Nat → Option Projection) :
    BVLogicalExpr := Id.run do
  -- Predicates that only occur below quantifiers have no entry yet.
  let entry := model.model[(⟨pred.pattern⟩ : Sym.ExprPtr)]?.getD {}
  let mut zeroCount := 0
  let mut oneCount := 0
  for (_, (output, _)) in entry.map do
    if output.bv.toNat == 0 then
      zeroCount := zeroCount + 1
    else if output.bv.toNat == 1 then
      oneCount := oneCount + 1

  let mut projs := #[]
  for projIdx in 0...pred.args.size do
    match proj projIdx with
    | none => projs := projs.push mkEqConst
    | some projDescr =>
      projs := projs.push fun arg input =>
        if h1 : projDescr.elseValue.w = input.w then
          let memInstSet := .not <| projDescr.values.foldl (init := .const true) fun acc normalVal =>
            .and acc (.not <| mkEqConst arg normalVal)
          let defaultCheck := mkEqConst arg input
          let projectedCheck := .const <| (projDescr.elseValue.bv.cast h1) == input.bv
          -- if arg ∈ instSet then arg == input else elseValue == input
          .ite memInstSet defaultCheck projectedCheck
        else
          unreachable!

  let defaultValue := if zeroCount ≤ oneCount then true else false
  let mut completedPred := .const false
  for ⟨input, ⟨output, _⟩⟩ in entry.map do
    if (output.bv.toNat == 1) == defaultValue then continue
    let mut isInput : BVLogicalExpr := .const true
    for h : argIdx in 0...pred.args.size do
      let arg := pred.args[argIdx]
      let inputVal := input[argIdx]!
      let projFn := projs[argIdx]!
      let guard := projFn arg inputVal
      isInput := .and isInput guard
    completedPred := .or completedPred isInput
  completedPred := if defaultValue == true then .not completedPred else completedPred
  return completedPred

end FunModel

/--
The model dependent information about a class of the instantiation set analysis that is not
unrestricted.
-/
structure RoundClass where
  /--
  The values of the terms in the instantiation set, without duplicates.
  -/
  values : Array BVExpr.PackedBitVec
  /--
  For each value the first term in the instantiation set that has it.
  -/
  inv : Std.HashMap BVExpr.PackedBitVec Expr
  /--
  The else value of the projection, if the class is used for projections.
  -/
  else? : Option BVExpr.PackedBitVec := none

/--
The projection of argument `idx` of the EPR predicate `pred` in the round described by `round`, if
any.
-/
def Projection.of? (instSets : EPR.InstSets) (round : Std.HashMap Nat RoundClass) (pred : Expr)
    (idx : Nat) : Option Projection := do
  let root ← instSets.posRoot[(pred, idx)]?
  let cls ← round[root]?
  return { values := cls.values, elseValue := ← cls.else? }

structure EprCtx where
  /--
  The model we are currently validating.
  -/
  cex : CegarM.CounterExample
  /--
  The instantiation set analysis.
  -/
  instSets : EPR.InstSets
  /--
  -/
  round : Std.HashMap Nat RoundClass

structure EprState where
  /--
  Here we record quantifiers and arguments we want to instantiate them with.
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

def mkAssumption (type : Expr) : Sym.SymM Normalize.Hyp := do
  let type ← Sym.shareCommon type
  return {
    name := .anonymous
    type
    value := ← mkSorry type true
    source := .epr
  }

namespace EprTemplate

/--
Collect the `Bool` UF atoms registered while reifying the template. Their patterns are the keys of
the same predicates in the `FunModel` of the main problem.
-/
def collectPredAtoms : ReifyM (Std.HashMap Nat EprTemplate.PredAtom) := do
  let funState := (← get).theoryState.funState
  let mut predAtoms := {}
  for funAtom in funState.atoms, mask in funState.masks, pattern in funState.patterns do
    unless funAtom.isBoolAtom do continue
    let some atomNumber ← ReifyM.getAtomNumber (← funAtom.atomExpr) | continue
    let (some args, lemmas) ← LemmaM.run (reifyArgs funAtom.funExpr.getAppArgs mask) | continue
    unless lemmas.isEmpty do continue
    predAtoms := predAtoms.insert atomNumber { pred? := (EPR.toBvPredApp? funAtom.funExpr).map (·.1), pattern, args }
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
      let hyps ← (guards.push negatedBody).mapM (mkAssumption ·)
      let exprs ← SubsolverT.reifyNormalized hyps
      let instConstAtoms ← SubsolverT.liftReifyM do
        let (atoms, _) ← LemmaM.run do
          fact.boundSorts.zip instConsts |>.mapM fun (sort, instConst) => do
            let atom ← Sym.share <| eprProblem.sortInfo[sort]!.appToBv instConst
            let some reified ← ReifiedBVExpr.of atom
              | throwError m!"Failed to reify MBQI constant {atom}"
            return (⟨reified.width, reified.bvExpr⟩ : (w : Nat) × BVExpr w)
        return atoms
      quants := quants.push { fact, instConsts, instConstAtoms, exprs }
    let predAtoms ← SubsolverT.liftReifyM collectPredAtoms
    return { reifyState := ← SubsolverT.getReifyState, quants, predAtoms }

structure Substitution where
  /--
  The EPR problem we are working on.
  -/
  template : EprTemplate
  /--
  The BitVec model we want to substitute in.
  -/
  cex : CegarM.CounterExample
  /--
  The UF model we want to substitute in.
  -/
  funModel : FunModel
  /--
  The projection of argument `idx` of the EPR predicate `pred` as `proj pred idx`.
  -/
  proj : Expr → Nat → Option Projection

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
    return s.funModel.completion atom fun idx => atom.pred?.bind (s.proj · idx)

end EprTemplate

/--
We pre-process and reify all quantifiers once, then substitute the models in on the reified
expression level during MBQI checks.
-/
def getEprTemplate : CegarM EprTemplate := do
  if let some template := (← CegarM.getTheoryState).eprState.template then
    return template
  let template ← EprTemplate.build
  CegarM.modifyTheoryState fun s => { s with eprState.template := some template }
  return template

namespace EprM

def run (template : EprTemplate) (cex : CegarM.CounterExample) (instSets : EPR.InstSets)
    (round : Std.HashMap Nat RoundClass) (x : EprM α) : CegarM (α × EprState) := do
  let ctx ← CegarM.getTacticContext
  let goal := (← read).goal
  let x := SubsolverT.run ctx goal x (reifyState := template.reifyState)
  StateRefT'.run (ReaderT.run x { cex, instSets, round }) {}

def recordInstance (hyp : EPR.QuantifiedFact) (args : Array Expr) : EprM Unit := do
  modifyThe EprState fun s => { s with instances := s.instances.push (hyp, args) }

/--
Record an instance of `hyp` with the values that `quantCex` assigns to `instConsts`. Whenever the
value is in `invs` for a variable we use the associated term of the instantiation set, otherwise the
first element of the sort that has the value.
-/
def recordCounterInst (hyp : EPR.QuantifiedFact) (quantCex : CegarM.CounterExample)
    (instConsts : Array Expr) (invs : Array (Option (Std.HashMap BVExpr.PackedBitVec Expr))) :
    EprM Unit := do
  let eprProblem := (← getThe BVDecide.State).theoryState.eprState.problem
  let sortInfos := hyp.boundSorts.map (eprProblem.sortInfo[·]!)
  let mut assignment := #[]
  for instConst in instConsts, sortInfo in sortInfos, inv? in invs do
    let atom := sortInfo.appToBv instConst
    let instConstVal := quantCex.exprCex[atom]!
    if let some term := inv?.bind (·[instConstVal]?) then
      assignment := assignment.push term
    else
      assignment := assignment.push <| ← recoverValue instConstVal sortInfo
  withTraceNode `Meta.Tactic.bv.epr (fun _ => return m!"New instance with: {assignment}") do
    recordInstance hyp assignment
where
  -- TODO: potentially cache
  recoverValue (value : BVExpr.PackedBitVec) (sortInfo : EPR.BvSortInfo) : EprM Expr := do
    for element in sortInfo.elements do
      let encodedElement := sortInfo.appToBv element
      let value' := (← read).cex.exprCex[encodedElement]!
      if value == value' then
        return element
    throwError m!"TODO: unreachable"

/--
`atom == v₁ || ... || atom == vₙ`.
-/
def mkRestriction (atom : (w : Nat) × BVExpr w) (values : Array BVExpr.PackedBitVec) :
    BVLogicalExpr :=
  values[1...*].foldl (init := mkEqConst atom values[0]!) fun disj value =>
    .or disj (mkEqConst atom value)

/--
Check whether the model violates `quant` at index `quantIdx`, given the reified expressions of
`quant` with the model substituted in.
-/
def checkQuant (quantIdx : Nat) (quant : EprTemplate.Quant) (exprs : Array BVLogicalExpr) :
    EprM Unit := do
  let hyp := quant.fact
  let instConsts := quant.instConsts
  withTraceNode `Meta.Tactic.bv.epr (fun _ => return m!"MBQI check for {hyp.hyp.type}") do
  let { instSets, round, .. } ← read
  -- If a round configuration does not contain an entry we assume the variable to be unrestricted
  -- Without `eprProjections` there are no classes.
  let classes := match instSets.varRoots[quantIdx]? with
    | some roots => roots.map (round[·]?)
    | none => hyp.boundSorts.map fun _ => none
  withTraceNode `Meta.Tactic.bv.epr (fun _ => return m!"Running consistency check") do
    SubsolverT.pushReified exprs
    let res ← SubsolverT.check
    match res with
    | .ok .. =>
      trace[Meta.Tactic.bv.epr] m!"Quantifier is consistent"
    | .error quantCex =>
      trace[Meta.Tactic.bv.epr] m!"Detected quantifier violation"
      /-
      We will now try to restrict the counterexample to the instantiation sets which will help guide
      the search closer towards already existing ground hypotheses.
      -/
      let invs := classes.map (·.map (·.inv))
      -- No need to perform a restricted check if the violation happens to be in the inst sets.
      if ← inInstSets hyp instConsts classes quantCex then
        recordCounterInst hyp quantCex instConsts invs
      else
        let mut restrictions := #[]
        for atom in quant.instConstAtoms, cls? in classes do
          let some cls := cls? | continue
          restrictions := restrictions.push <| mkRestriction atom cls.values
        SubsolverT.pushReified restrictions
        let restrictedRes ← SubsolverT.check
        SubsolverT.pop
        match restrictedRes with
        | .ok .. =>
          -- If the restricted check did not manage to find a refined instance, return the
          -- unrestricted one.
          trace[Meta.Tactic.bv.epr] m!"No violation within the instantiation sets"
          recordCounterInst hyp quantCex instConsts invs
        | .error restrictedCex =>
          -- If the restricted check manage to find a refined instance, return that instance.
          recordCounterInst hyp restrictedCex instConsts invs
    SubsolverT.pop
where
  inInstSets (hyp : EPR.QuantifiedFact) (instConsts : Array Expr)
      (classes : Array (Option RoundClass)) (quantCex : CegarM.CounterExample) : EprM Bool := do
    let eprProblem := (← getThe BVDecide.State).theoryState.eprState.problem
    for instConst in instConsts, cls? in classes, sort in hyp.boundSorts do
      let some cls := cls? | continue
      let value := quantCex.exprCex[eprProblem.sortInfo[sort]!.appToBv instConst]!
      if !cls.inv.contains value then return false
    return true

end EprM

def checkModel (template : EprTemplate) : EprM Unit := do
  let funModel := (← getThe CegarM.State).theoryState.funState.currentModel
  let { instSets, round, cex } ← read
  let subst : EprTemplate.Substitution :=
    { template, cex, funModel, proj := Projection.of? instSets round }
  let exprs := BVLogicalExpr.substituteAll subst (template.quants.flatMap (·.exprs))
  let mut offset := 0
  for h : idx in 0...template.quants.size do
    let quant := template.quants[idx]
    let next := offset + quant.exprs.size
    EprM.checkQuant idx quant exprs[offset...next].toArray
    offset := next

/--
Compute the model dependent information about the instantiation sets. Like Z3 an empty
instantiation set is treated as if it contained the default element of its sort.
-/
def mkRound (instSets : EPR.InstSets) (cex : CegarM.CounterExample) (problem : EPR.EprBvProblem) :
    Std.HashMap Nat RoundClass := Id.run do
  let eval (sort : EPR.SortId) (e : Expr) : BVExpr.PackedBitVec :=
    cex.exprCex[problem.sortInfo[sort]!.appToBv e]!
  let mut round := {}
  for (root, cls) in instSets.classes do
    if cls.full then continue
    let terms := if cls.terms.isEmpty then #[problem.sortInfo[cls.sort]!.default] else cls.terms
    let mut values := #[]
    -- An inversion of the model for the elements in this class.
    let mut inv := {}
    for term in terms do
      let value := eval cls.sort term
      unless inv.contains value do
        values := values.push value
        inv := inv.insert value term
    -- If the instantiation set covers the whole sort, projections and restrictions are the identity.
    let covers := problem.sortInfo[cls.sort]!.elements.all fun elem =>
      inv.contains (eval cls.sort elem)
    if covers then continue
    round := round.insert root { values, inv }
  /-
  We now attempt to find an else value for each predicate position that has a variable occuring in
  it. This must respect:
  1. The else value MUST be one of the values assigned to a member of the equivalence class of that
     position.
  2. The else value SHOULD not take the same value as one of the values for the ground terms
     recorded in the exception set. 
  3. The else value SHOULD not take the same value as one of the else values of the classes recorded
     in the avoid set. As this imposes an implicit dependency graph onto the else values, we try
     to make this computation more deterministic by iterating in a somewhat predictable order.
  If the optional criteria cannot be met, we just choose the value of the first member of the
  equivalence class.
  -/
  let projRoots := Std.HashSet.ofArray instSets.posRoot.valuesArray |>.toArray.qsort (· < ·)
  for root in projRoots do
    let some roundCls := round[root]? | continue
    let cls := instSets.classes[root]!
    let mut avoid : Std.HashSet BVExpr.PackedBitVec := {}
    for exception in cls.exceptions do
      let value := eval cls.sort exception
      avoid := avoid.insert value
    for other in cls.avoid do
      if let some otherRoundCls := round[other]? then
        if let some value := otherRoundCls.else? then
          avoid := avoid.insert value
    let elseValue := roundCls.values.find? (!avoid.contains ·) |>.getD roundCls.values[0]!
    round := round.insert root { roundCls with else? := some elseValue }
  return round

/--
Get the instantiation sets, running the analysis if this is the first MBQI round.
-/
def getInstSets : CegarM EPR.InstSets := do
  if let some instSets := (← CegarM.getTheoryState).eprState.instSets then
    return instSets
  let problem := (← getThe BVDecide.State).theoryState.eprState.problem
  let mut instSets ← EPR.InstSets.build problem
  for hyp in (← readThe BVDecide.Context).hypotheses do
    instSets ← instSets.addGround hyp.type
  instSets.traceAnalysis
  CegarM.modifyTheoryState fun s => { s with eprState.instSets := some instSets }
  return instSets

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
  let config := (← CegarM.getTacticContext).config
  unless config.epr do return false
  let instSets ← do
    if config.eprProjections then
      let sets ← getInstSets
      sets.traceSets
      pure sets
    else
      pure {}
  let round := mkRound instSets cex (← getThe BVDecide.State).theoryState.eprState.problem
  let template ← getEprTemplate
  let (_, s) ← EprM.run template cex instSets round do
    checkModel template
  let mut instSets := instSets
  for (hyp, args) in s.instances do
    let inst ← instantiateWithoutGuards hyp args
    trace[Meta.Tactic.bv.epr] m!"Instance: {inst}"
    if config.eprProjections then
      instSets ← instSets.addGround inst.type
    CegarM.pushNewHyp {
      hyp := inst
      tacticProof := throwError m!"Cannot squeeze EPR proofs TODO"
      grindProof := throwError m!"Cannot squeeze EPR proofs TODO"
      isNormalized := true -- TODO: contemplate
    }
  if config.eprProjections then
    CegarM.modifyTheoryState fun s => { s with eprState.instSets := some instSets }
  return !s.instances.isEmpty

end Cegar

end Lean.Meta.Tactic.BVDecide
