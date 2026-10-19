/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.EPR.Basic
import Std.Tactic.BVDecide.EPR.BitVec
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.AbstractS
import Lean.Meta.AppBuilder
import Init.Data.Range.Polymorphic.Iterators

/-!
This module performs the translation from a regular `EprProblem` to an BitVec encoded
`EprBvProblem`.
-/

namespace Lean.Meta.Tactic.BVDecide.EPR

/--
Information about a quantified variable.
-/
structure VarInfo where
  /--
  The sort the variable belongs to.
  -/
  sort : SortId
  /--
  A proof that the variable itself is a member of the element list of its sort.
  -/
  memElemsProof : Expr
  deriving Inhabited

structure TranslateCtx where
  /--
  Information about the predicates used in the problem.
  -/
  predInfo : Std.HashMap Expr BvPredInfo
  /--
  Information about the sorts used in the problem.
  -/
  sortInfo : Std.HashMap SortId BvSortInfo
  /--
  A map from sort elements to their sort. Note that this does not include quantified variables.
  -/
  sortMap : Std.HashMap Expr SortId
  /--
  Information about quantified variables.
  -/
  varMap : Std.HashMap Expr VarInfo := {}

namespace TranslateCtx

def getSort? (ctx : TranslateCtx) (e : Expr) : Option SortId :=
  if let some sort := ctx.sortMap[e]? then
    some sort
  else
    ctx.varMap[e]?.map (·.sort)

/--
A proof that `e` is a member of the element list of its sort.
-/
def getMemProof? (ctx : TranslateCtx) (e : Expr) : Option Expr :=
  if let some info := ctx.varMap[e]? then
    some info.memElemsProof
  else if let some sort := ctx.sortMap[e]? then
    ctx.sortInfo[sort]!.elemListMemProofs[e]?
  else
    none

end TranslateCtx

def translateAtom (ctx : TranslateCtx) : Sym.Simp.Simproc := fun e => do
  match_expr e with
  | Eq α lhs rhs =>
    let some sort := ctx.getSort? lhs | return .rfl
    let some lhsMem := ctx.getMemProof? lhs | return .rfl
    let some rhsMem := ctx.getMemProof? rhs | return .rfl
    let sortInfo := ctx.sortInfo[sort]!
    let resExpr ← Sym.share <|
      mkApp3 (mkConst ``Eq [1]) sortInfo.bvType (sortInfo.appToBv lhs) (sortInfo.appToBv rhs)
    let resProof :=
      mkApp8 (mkConst ``Std.Tactic.BVDecide.EPR.BitVec.eq_eq_toBvAux_eq_of_mem [sortInfo.level])
        α
        (toExpr sortInfo.width)
        sortInfo.elemList
        sortInfo.elemListLt
        lhs
        rhs
        lhsMem
        rhsMem
    return .step resExpr resProof (done := true)
  | _ =>
    e.withApp fun pred args => do
      let some predInfo := ctx.predInfo[pred]? | return .rfl
      if args.size != predInfo.argumentSorts.size then return .rfl
      let mut resExpr := predInfo.bvPred
      let mut resProof := predInfo.eqThm
      for arg in args, sort in predInfo.argumentSorts do
        let some argMem := ctx.getMemProof? arg | return .rfl
        let sortInfo := ctx.sortInfo[sort]!
        resExpr := mkApp resExpr (sortInfo.appToBv arg)
        resProof := mkApp2 resProof arg argMem
      resExpr ← Sym.share <| mkApp3 (mkConst ``Eq [1]) (toTypeExpr (BitVec 1)) resExpr (toExpr 1#1)
      return .step resExpr resProof (done := true)

structure TranslateState where
  simpCache : Sym.Simp.Cache := {}
  memHypThmsCache : Std.HashMap SortId Sym.Simp.Theorems := {}

abbrev TranslateExprM := ReaderT TranslateCtx StateRefT TranslateState Sym.SymM

namespace TranslateExprM

def run (ctx : TranslateCtx) (x : TranslateExprM α) : Sym.SymM α := do
  StateRefT'.run' (ReaderT.run x ctx) {}

@[inline]
def withVarMap (varMap : Std.HashMap Expr VarInfo) (x : TranslateExprM α) : TranslateExprM α :=
  withReader (fun ctx => { ctx with varMap }) do
    x

@[inline]
def getSortInfo (sort : SortId) : TranslateExprM BvSortInfo := do
  return (← read).sortInfo[sort]!

def translateProp (type value : Expr) : TranslateExprM (Expr × Expr) := do
  let methods := { pre := translateAtom (← read) }
  let simpState := { persistentCache := ← takeSimpCache }
  let (res, s) ← Sym.Simp.SimpM.run (methods := methods) (s := simpState) do
    Sym.Simp.simp type
  modify fun st => { st with simpCache := s.persistentCache }
  match res with
  | .rfl .. => return (type, value)
  | .step type' proof .. => return (type', mkApp4 (mkConst ``Eq.mp [0]) type type' proof value)
where
  takeSimpCache : TranslateExprM Sym.Simp.Cache := do
    modifyGet fun s => (s.simpCache, { s with simpCache := {} })

end TranslateExprM

def translateGround (hyp : Normalize.Hyp) : TranslateExprM Normalize.Hyp := do
  let (type, value) ← TranslateExprM.translateProp hyp.type hyp.value
  return { hyp with type, value }

def translateQuantified (hyp : QuantifiedFact) : TranslateExprM QuantifiedFact := do
  forallBoundedTelescope hyp.hyp.type hyp.boundSorts.size fun args body => do
    let body ← Sym.shareCommon body
    assert! args.size == hyp.boundSorts.size
    let mut memHypDisjs := #[]
    let mut memHypOfs := #[]
    for arg in args, sort in hyp.boundSorts do
      let (memHypDisj, memHypOf) ← mkMemHyp arg sort
      memHypDisjs := memHypDisjs.push (.anonymous, memHypDisj)
      memHypOfs := memHypOfs.push memHypOf
    withLocalDeclsDND memHypDisjs fun memHypDisjs => do
      let mut varMap := {}
      for memHypDisj in memHypDisjs, memHypOf in memHypOfs, sort in hyp.boundSorts, arg in args do
        varMap := varMap.insert arg { sort, memElemsProof := mkApp memHypOf memHypDisj }
      TranslateExprM.withVarMap varMap do
        let (body, bodyProof) ← TranslateExprM.translateProp body (mkAppN hyp.hyp.value args)
        let resExpr ← Sym.mkForallFVarsS (args ++ memHypDisjs) body
        let resProof ← mkLambdaFVars (args ++ memHypDisjs) bodyProof
        return { hyp with hyp.type := resExpr, hyp.value := resProof }
where
  /--
  Compute:
  1. `to_bv expr = to_bv sortList[0] ∨ ... ∨ to_bv expr = to_bv sortList[n]`
  2. a proof that this implies `expr ∈ sortList`
  -/
  mkMemHyp (expr : Expr) (sortId : SortId) : TranslateExprM (Expr × Expr) := do
    let sortInfo ← TranslateExprM.getSortInfo sortId
    let thms ←
      if let some thms := (← get).memHypThmsCache[sortId]? then
        pure thms
      else
        let mut thms : Sym.Simp.Theorems := {}
        let thm :=
          mkApp4 (mkConst ``Std.Tactic.BVDecide.EPR.BitVec.mem_iff_toBvAux_mem_map_toBvAux [sortInfo.level])
            sortInfo.type
            (toExpr sortInfo.width)
            sortInfo.elemList
            sortInfo.elemListLt
        thms := thms.insert (← Sym.Simp.mkTheoremFromExpr thm)
        thms := thms.insert (← Sym.Simp.mkTheoremFromDecl ``Std.Tactic.BVDecide.EPR.BitVec.mem_map_nil)
        thms := thms.insert (← Sym.Simp.mkTheoremFromDecl ``Std.Tactic.BVDecide.EPR.BitVec.mem_map_cons_cons)
        thms := thms.insert (← Sym.Simp.mkTheoremFromDecl ``Std.Tactic.BVDecide.EPR.BitVec.mem_map_singleton)
        modify fun s => { s with memHypThmsCache := s.memHypThmsCache.insert sortId thms }
        pure thms

    let mem ← Sym.share <| ← mkAppM ``Membership.mem #[sortInfo.elemList, expr]
    let .step mem' eq ← Sym.simp mem { pre := thms.rewrite }
      | throwError m!"Simplifying {mem} made no progress"
    let proof := mkApp3 (mkConst ``Eq.mpr [0]) mem mem' eq
    return (mem', proof)

def translatePreds (preds : Std.HashMap Expr PredInfo) (sortInfos : Std.HashMap SortId BvSortInfo) :
    Sym.SymM (Std.HashMap Expr BvPredInfo) := do
  let mut newInfos := {}
  for (pred, predInfo) in preds do
    if predInfo.argumentSorts.size > 16 then
      throwError m!"EPR predicates with more than 16 arguments are not supported yet: {pred}"
    if predInfo.argumentSorts.isEmpty then
      throwError m!"EPR predicates should not have arity 0"
    let (bvPredBase, eqBase) := arityMap[predInfo.argumentSorts.size - 1]!
    let levels := predInfo.argumentSorts.map (sortInfos[·]!.level) |>.toList
    let mut bvPred := mkConst bvPredBase levels
    let mut eqThm := mkConst eqBase levels
    for sort in predInfo.argumentSorts do
      let sortInfo := sortInfos[sort]!
      bvPred := mkApp4 bvPred sortInfo.type (toExpr sortInfo.width) sortInfo.elemList sortInfo.default
      eqThm := mkApp5 eqThm sortInfo.type (toExpr sortInfo.width) sortInfo.elemList sortInfo.elemListLt sortInfo.default
    bvPred ← Sym.share <| mkApp bvPred pred
    eqThm := mkApp eqThm pred
    newInfos := newInfos.insert pred { predInfo with bvPred, eqThm }
  return newInfos
where
  arityMap : Array (Name × Name) := #[
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₂, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₂_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₃, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₃_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₄, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₄_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₅, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₅_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₆, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₆_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₇, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₇_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₈, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₈_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₉, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₉_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₀, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₀_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₁, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₁_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₂, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₂_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₃, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₃_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₄, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₄_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₅, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₅_toBvAux_eq),
    (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₆, ``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₆_toBvAux_eq),
  ]

def translateSorts (sorts : Std.HashMap SortId SortInfo) :
    Sym.SymM (Std.HashMap SortId BvSortInfo × Array Normalize.Hyp) := do
  let mut bvSortInfo := Std.HashMap.emptyWithCapacity sorts.size
  let mut facts := #[]
  for (sortId, sortInfo) in sorts do
    let width := sortInfo.card.log2 + 1
    let elemList ← Sym.share <| ← mkListLit sortInfo.type sortInfo.elements.toList
    let elemListLt ← mkDecideProof (← mkLt (← mkAppM ``List.length #[elemList]) (toExpr (2^width)))
    let toBv ← Sym.share <| mkApp4 (mkConst ``Std.Tactic.BVDecide.EPR.BitVec.toBvAux [sortInfo.level]) sortInfo.type (toExpr width) elemList elemListLt
    let toSort ← Sym.share <| mkApp4 (mkConst ``Std.Tactic.BVDecide.EPR.BitVec.toSortAux [sortInfo.level]) sortInfo.type (toExpr width) elemList sortInfo.default
    let mut elemListMemProofs := {}
    for idx in 0...sortInfo.card do
      let element := sortInfo.elements[idx]!
      let memProof :=
        mkApp6 (mkConst ``List.mem_of_getElem [sortInfo.level])
          sortInfo.type
          elemList
          (toExpr idx)
          (← mkDecideProof (← mkLt (toExpr idx) sortInfo.cardExpr))
          element
          (← mkAppM ``eagerReduce #[← mkEqRefl element])
      elemListMemProofs := elemListMemProofs.insert element memProof
      let type ← Sym.share <| ← mkLt (mkApp toBv element) (toExpr (BitVec.ofNat width sortInfo.elements.size))
      let proof :=
        mkApp6 (mkConst ``Std.Tactic.BVDecide.EPR.BitVec.toBvAux_lt_ofNat_length_of_mem [sortInfo.level])
          sortInfo.type
          (toExpr width)
          elemList
          elemListLt
          element
          memProof
      facts := facts.push {
        name := .anonymous
        type := type
        value := proof
        source := .epr
      }
    let sortInfo := { sortInfo with width, toBv, elemList, elemListLt, elemListMemProofs, toSort }
    bvSortInfo := bvSortInfo.insert sortId sortInfo
  return (bvSortInfo, facts)

public def epr2BitVec (problem : EprProblem) (g : MVarId) : Sym.SymM EprBvProblem := g.withContext do
  let (sortInfo, additionalFacts) ← translateSorts problem.sortInfo
  let predInfo ← translatePreds problem.predInfo sortInfo
  TranslateExprM.run { predInfo, sortInfo, sortMap := problem.sortMap } do
    let groundFacts ← problem.groundFacts.mapM translateGround
    let quantifiedFacts ← problem.quantifiedFacts.mapM translateQuantified
    return {
      sortInfo := sortInfo,
      sortMap := problem.sortMap -- TODO: think about whether we should refer to BV constants here
      predInfo := predInfo
      groundFacts := groundFacts ++ additionalFacts
      quantifiedFacts := quantifiedFacts
    }

end Lean.Meta.Tactic.BVDecide.EPR
