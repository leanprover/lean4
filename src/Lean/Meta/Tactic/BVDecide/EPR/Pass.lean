/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
public import Lean.Meta.Tactic.BVDecide.EPR.BitVec
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Sym.InferType

/-!
This module implements the EPR detection pass which encodes a many-sorted EPR problem in the hypotheses into
`BitVec`.
-/

namespace Lean.Meta.Tactic.BVDecide.EPR

open Normalize

/--
Information about a candidate for an EPR sort.
-/
structure SortCandidate where
  /--
  The Lean level type of the sort.
  -/
  type : Expr
  /--
  The universe level of `type`
  -/
  level : Level
  /--
  The potential elements of the aspiring sort.
  -/
  elements : Array Expr := #[]
  deriving Inhabited

public structure DetectResult where
  problem : EprProblem
  /--
  The hyps that are not part of `problem`.
  -/
  remainingHyps : Array Hyp

structure DetectState where
  /--
  Information about current sort candidates.
  -/
  sorts : Std.HashMap SortId SortCandidate := {}
  /--
  Map from types to their respective sort.
  -/
  sortIds : Std.HashMap Sym.ExprPtr SortId := {}
  /--
  Name generator for sorts.
  -/
  nextSortId : Nat := 0
  /--
  Map from sort elements (fvars from the local context) to their respective sort.
  -/
  elements : Std.HashMap Sym.ExprPtr SortId := {}
  /--
  Information about current predicate candidates.
  -/
  preds : Std.HashMap Sym.ExprPtr PredInfo := {}
  groundFacts : Array Hyp := #[]
  quantifiedFacts : Array QuantifiedFact := #[]
  /--
  The hyps that are not part of the problem.
  -/
  remainingHyps : Array Hyp := #[]

abbrev DetectM := StateRefT DetectState Sym.SymM

namespace DetectM

@[inline]
def run (x : DetectM α) : Sym.SymM α :=
  StateRefT'.run' x {}

@[inline]
def getSort? (type : Expr) : DetectM (Option SortId) :=
  let ptr : Sym.ExprPtr := ⟨type⟩
  return (← get).sortIds[ptr]?

def registerSort (type : Expr) (level : Level) : DetectM Unit := do
  let type ← Sym.share type
  modify fun s =>
    let id := ⟨s.nextSortId⟩
    { s with
      sorts := s.sorts.insert id { type, level }
      sortIds := s.sortIds.insert ⟨type⟩ id
      nextSortId := s.nextSortId + 1
    }

def registerElement (elem : Expr) (sort : SortId) : DetectM Unit := do
  let elem ← Sym.share elem
  modify fun s =>
    { s with
      sorts := s.sorts.modify sort fun info => { info with elements := info.elements.push elem }
      elements := s.elements.insert ⟨elem⟩ sort
    }

def registerPred (pred : Expr) (argumentSorts : Array SortId) : DetectM Unit := do
  let pred ← Sym.share pred
  modify fun s => { s with preds := s.preds.insert ⟨pred⟩ { argumentSorts } }

/--
Check whether `type` is a non-dependent function of the shape `α₁ → ... → αₙ → Prop` where
all `α` are EPR sorts.
-/
def predType? (type : Expr) : DetectM (Option (Array SortId)) :=
  go type #[]
where
  go (type : Expr) (acc : Array SortId) : DetectM (Option (Array SortId)) := do
    match type with
    | .sort .zero => return if acc.isEmpty then none else some acc
    | .forallE _ dom body _ =>
      if body.hasLooseBVars then return none
      let some sort ← getSort? dom | return none
      go body (acc.push sort)
    | _ => return none

/--
Try to identify potential candidates for EPR sorts, their elements and predicates.

We say a type `α` is a potential candidate if `α : Type u` for some level `u`.

We say a `p` is an EPR predicate if `p : α₁ → ... → αₙ → Prop` with `n > 0` where all `α` are
candidates.
-/
def processLocalDecl (decl : LocalDecl) : DetectM Unit := do
  if decl.isImplementationDetail || decl.isLet then return
  let type ← Sym.instantiateMVarsS decl.type
  if let .sort (.succ u) := type then
    registerSort (← Sym.share decl.toExpr) u
  else if let some sort ← getSort? type then
    registerElement (← Sym.share decl.toExpr) sort
  else if let some argumentSorts ← predType? type then
    registerPred (← Sym.share decl.toExpr) argumentSorts

structure ScanContext where
  /--
  If we have an hypothesis with leading quantifiers, these are the sorts of the quantifiers.
  -/
  boundSorts : Array SortId

structure ScanState where
  /--
  Whether the analyzed fact mentions an element or predicate of a sort.
  -/
  mentionsSort : Bool := false
  /--
  Cache for `checkProp`.
  -/
  cache : Std.HashSet (Sym.ExprPtr × Nat) := {}

abbrev ScanM := ReaderT ScanContext StateRefT ScanState DetectM

namespace ScanM

@[inline]
def markMentionsSort : ScanM Unit :=
  modify fun s => { s with mentionsSort := true }

def checkTerm (e : Expr) (depth : Nat) : ScanM (Option SortId) := do
  match e with
  | .bvar idx =>
    if idx < depth then return none
    let boundSorts := (← read).boundSorts
    let idx := idx - depth
    return boundSorts[boundSorts.size - 1 - idx]?
  | _ =>
    let ptr : Sym.ExprPtr := ⟨e⟩
    let some sort := (← getThe DetectState).elements[ptr]? | return none
    markMentionsSort
    return some sort

def checkEq (α lhs rhs : Expr) (depth : Nat) : ScanM Bool := do
  let some sort ← getSort? α | return false
  let some lhsSort ← checkTerm lhs depth | return false
  let some rhsSort ← checkTerm rhs depth | return false
  return lhsSort == sort && rhsSort == sort

def checkPredApp (e : Expr) (depth : Nat) : ScanM Bool := do
  e.withApp fun pred args => do
    let predPtr : Sym.ExprPtr := ⟨pred⟩
    let some info := (← getThe DetectState).preds[predPtr]? | return false
    if args.size != info.argumentSorts.size then return false
    for arg in args, sort in info.argumentSorts do
      let some argSort ← checkTerm arg depth | return false
      if argSort != sort then return false
    markMentionsSort
    return true

/--
Check that `e` is approximately a quantifier free EPR expression. `depth` is the amount of `forallE`
we are under.
-/
partial def checkProp (e : Expr) (depth : Nat) : ScanM Bool := do
  goCache e depth
where
  goCache (e : Expr) (depth : Nat) : ScanM Bool := do
    if (← get).cache.contains (⟨e⟩, depth) then
      return true
    else
      let value ← go e depth
      if value then
        modify fun s => { s with cache := s.cache.insert (⟨e⟩, depth) }
        return true
      else
        return false

  go (e : Expr) (depth : Nat) : ScanM Bool := do
    match e with
    | .forallE _ dom body _ =>
      if body.hasLooseBVar 0 then return false
      goCache dom depth <&&> goCache body (depth + 1)
    | _ =>
      match_expr e with
      | True => return true
      | False => return true
      | Not p => goCache p depth
      | And p q => goCache p depth <&&> goCache q depth
      | Or p q => goCache p depth <&&> goCache q depth
      | Iff p q => goCache p depth <&&> goCache q depth
      | Eq α lhs rhs =>
        if α.isProp then
          goCache lhs depth <&&> goCache rhs depth
        else
          checkEq α lhs rhs depth
      | _ => checkPredApp e depth <||> isPropAtom e

  isPropAtom (e : Expr) : ScanM Bool := do
    match e with
    | .fvar fvarId => return (← fvarId.getType).isProp
    | .const declName _ => return (← getConstVal declName).type.isProp
    | _ => return false


end ScanM

/--
Check whether `hyp` is a, potentially universally quantified, EPR hypothesis.
-/
def checkFact? (hyp : Hyp) : DetectM (Option (Array SortId)) := do
  let (boundSorts, body) ← stripQuantifiers hyp.type #[]
  let sorts := (← get).sorts
  if boundSorts.any (sorts[·]!.elements.isEmpty) then
    trace[Meta.Tactic.bv.epr] m!"Discarding fact as it mentions empty sorts: {hyp.type}"
    return none
  let (ok, { mentionsSort, .. }) ← ScanM.checkProp body 0 |>.run { boundSorts } |>.run {}
  if !ok || (boundSorts.isEmpty && !mentionsSort) then
    return none
  else
    return some boundSorts
where
  stripQuantifiers (type : Expr) (acc : Array SortId) : DetectM (Array SortId × Expr) := do
    let .forallE _ dom body _ := type | return (acc, type)
    let some sort ← getSort? dom | return (acc, type)
    stripQuantifiers body (acc.push sort)

def processHyp (hyp : Hyp) : DetectM Unit := do
  match ← checkFact? hyp with
  | none => modify fun s => { s with remainingHyps := s.remainingHyps.push hyp }
  | some #[] => modify fun s => { s with groundFacts := s.groundFacts.push hyp }
  | some boundSorts =>
    modify fun s => { s with quantifiedFacts := s.quantifiedFacts.push { hyp, boundSorts } }

/--
Infers an element from a `Nonempty` instance for each sort that does not have any elements yet.
-/
def ensureHasElement : DetectM Unit := do
  for (sort, info) in (← get).sorts do
    unless info.elements.isEmpty do continue
    let u := mkLevelSucc info.level
    if let some inst ← synthInstance? (mkApp (mkConst ``Nonempty [u]) info.type) then
      let elem ← Sym.share <| mkApp2 (mkConst ``Classical.ofNonempty [u]) info.type inst
      registerElement elem sort

def assemble : DetectM DetectResult := do
  let s ← get
  let mut problem : EprProblem := { groundFacts := s.groundFacts, quantifiedFacts := s.quantifiedFacts }
  for (sort, info) in s.sorts do
    if info.elements.isEmpty then continue
    problem := { problem with
      sortInfo := problem.sortInfo.insert sort {
        type := info.type
        level := info.level
        elements := info.elements
      }
      sortMap := info.elements.foldl (init := problem.sortMap) (·.insert · sort) }
  for (pred, info) in s.preds do
    if info.argumentSorts.all problem.sortInfo.contains then
      problem := { problem with predInfo := problem.predInfo.insert pred.expr info }
  return { problem, remainingHyps := s.remainingHyps }

end DetectM

public def detectEprProblem (hyps : Array Hyp) : Sym.SymM DetectResult := do
  DetectM.run do
    (← getLCtx).forM DetectM.processLocalDecl
    DetectM.ensureHasElement
    hyps.forM DetectM.processHyp
    DetectM.assemble

def traceProblem (problem : EprProblem) : MetaM Unit := do
  withTraceNode `Meta.Tactic.bv.epr (fun _ => return m!"Detected EPR problem") do
    let sorts := problem.sortInfo.toArray.qsort (·.1.idx < ·.1.idx)
    for (_, info) in sorts do
      trace[Meta.Tactic.bv.epr] m!"sort {info.type} with elements {info.elements}"
    let preds := problem.predInfo.toArray.qsort (·.1.lt ·.1)
    for (pred, info) in preds do
      let argumentSorts := info.argumentSorts.map (problem.sortInfo[·]!.type)
      trace[Meta.Tactic.bv.epr] m!"predicate {pred} over {argumentSorts}"
    for fact in problem.groundFacts do
      trace[Meta.Tactic.bv.epr] m!"ground fact: {fact.type}"
    for fact in problem.quantifiedFacts do
      trace[Meta.Tactic.bv.epr] m!"quantified fact: {fact.hyp.type}"

def detectAndEncode (g : MVarId) (hyps : Array Hyp) :
    Sym.SymM (Option (Array Hyp × EprBvProblem)) := g.withContext do
  let { problem, remainingHyps } ← detectEprProblem hyps
  if problem.groundFacts.isEmpty && problem.quantifiedFacts.isEmpty then return none
  traceProblem problem
  -- TODO: Pre-Processing here.
  let bvProblem ← epr2BitVec problem g
  return some (remainingHyps, bvProblem)

public def eprDetectPass : Pass where
  name := `eprDetectPass
  run' := do
    let g ← PreProcessM.getTargetMVarId
    let some (remainingHyps, bvProblem) ← detectAndEncode g (← PreProcessM.getHyps) | return false
    modify fun s => { s with hypotheses := remainingHyps, eprBvProblem := bvProblem }
    PreProcessM.addHyps bvProblem.groundFacts
    return false

end Lean.Meta.Tactic.BVDecide.EPR
