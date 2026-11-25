/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.EPR.Basic
public import Std.Tactic.BVDecide.Syntax
import Std.Tactic.BVDecide.EPR.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
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
  | Std.Tactic.BVDecide.Bool.ofProp _p => return .rfl (done := true)
  | Eq α lhs rhs =>
    if α.isProp then
      let resExpr ← Sym.share <| mkIff lhs rhs
      let resProof := mkApp3 (mkConst ``propext) e resExpr (mkApp2 (mkConst ``eq_iff_iff) lhs rhs)
      return .step resExpr resProof
    else
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
  | Std.Tactic.BVDecide.EPR.BitVec.toBvAux _ _ _ _ _ =>
    -- fast path so we avoid visiting the membership list.
    return .rfl (done := true)
  | _ =>
    if e.isFVar then
      unless (← e.fvarId!.getType).isProp do return .rfl
      let resExpr ← Sym.share <|
        mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
          (mkApp (mkConst ``Std.Tactic.BVDecide.Bool.ofProp) e) (toExpr true)
      let resProof := mkApp (mkConst ``Std.Tactic.BVDecide.Bool.eq_ofProp_eq_true) e
      return .step resExpr resProof (done := true)
    else
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
        if predInfo.encoding == .prop then
          resExpr ← Sym.share <| mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) resExpr (toExpr true)
        return .step resExpr resProof (done := true)

structure TranslateState where
  simpCache : Sym.Simp.Cache := {}

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
  /-
  Re-using this cache across multiple quantifiers is sound as long as FVarId's created by
  telescopes remain unique. This is because the only thing affected by the quantifier dependent part
  of the context we pass into `translateAtom` is the rewriting of free variables.
  -/
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
    let mut guards := #[]
    for arg in args, sort in hyp.boundSorts do
      let guard ← Sym.share <| (← TranslateExprM.getSortInfo sort).mkGuard arg
      guards := guards.push (.anonymous, guard)
    withLocalDeclsDND guards fun guards => do
      let mut varMap := {}
      for guard in guards, sort in hyp.boundSorts, arg in args do
        let memElemsProof := (← TranslateExprM.getSortInfo sort).mkMemProofOfGuard arg guard
        varMap := varMap.insert arg { sort, memElemsProof }
      TranslateExprM.withVarMap varMap do
        let (body, bodyProof) ← TranslateExprM.translateProp body (mkAppN hyp.hyp.value args)
        let resExpr ← Sym.mkForallFVarsS (args ++ guards) body
        let resProof ← mkLambdaFVars (args ++ guards) bodyProof
        return { hyp with hyp.type := resExpr, hyp.value := resProof }

def translatePreds (preds : Std.HashMap Expr PredInfo) (sortInfos : Std.HashMap SortId BvSortInfo) :
    Sym.SymM (Std.HashMap Expr BvPredInfo) := do
  let mut newInfos := {}
  for (pred, predInfo) in preds do
    if predInfo.argumentSorts.size > Std.Tactic.BVDecide.EPR.BitVec.maxToBvPredArity then
      throwError m!"EPR predicates with more than {Std.Tactic.BVDecide.EPR.BitVec.maxToBvPredArity} arguments are not supported yet: {pred}"
    if predInfo.argumentSorts.isEmpty then
      throwError m!"EPR predicates should not have arity 0"
    let (bvPredBase, eqBase) :=
      match predInfo.encoding with
      | .prop => Std.Tactic.BVDecide.EPR.BitVec.toBvPredPropDecls[predInfo.argumentSorts.size - 1]!
      | .bool => Std.Tactic.BVDecide.EPR.BitVec.toBvPredBoolDecls[predInfo.argumentSorts.size - 1]!
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

def translateSorts (sorts : Std.HashMap SortId SortInfo)
    (symBreak : Elab.Tactic.BVDecide.EprSymBreak) :
    Sym.SymM (Std.HashMap SortId BvSortInfo × Array Normalize.Hyp) := do
  let mut bvSortInfo := Std.HashMap.emptyWithCapacity sorts.size
  let mut facts := #[]
  for (sortId, sortInfo) in sorts do
    let width := sortInfo.card.log2 + 1
    let elemList ← Sym.share <| ← mkListLit sortInfo.type sortInfo.elements.toList
    let elemListLength ← mkAppM ``List.length #[elemList]
    let elemListLt ← mkDecideProof (← mkLt elemListLength (toExpr (2^width)))
    let elemListLength ← mkDecideProof (← mkEq elemListLength sortInfo.cardExpr)
    let toBv ← Sym.share <| mkApp4 (mkConst ``Std.Tactic.BVDecide.EPR.BitVec.toBvAux [sortInfo.level]) sortInfo.type (toExpr width) elemList elemListLt
    let toSort ← Sym.share <| mkApp4 (mkConst ``Std.Tactic.BVDecide.EPR.BitVec.toSortAux [sortInfo.level]) sortInfo.type (toExpr width) elemList sortInfo.default
    let bvLit (n : Nat) : Expr := toExpr (BitVec.ofNat width n)
    let mkFact (type value : Expr) : Normalize.Hyp :=
      { name := .anonymous, type, value, source := .epr }
    let mut elemListMemProofs := {}
    for idx in 0...sortInfo.card do
      let element := sortInfo.elements[idx]!
      let idxLt ← mkDecideProof (← mkLt (toExpr idx) sortInfo.cardExpr)
      let getElemEq ← mkAppM ``eagerReduce #[← mkEqRefl element]
      let memProof :=
        mkApp6 (mkConst ``List.mem_of_getElem [sortInfo.level])
          sortInfo.type
          elemList
          (toExpr idx)
          idxLt
          element
          getElemEq
      elemListMemProofs := elemListMemProofs.insert element memProof
      if symBreak matches .off then
        let type ← Sym.share <| ← mkLt (mkApp toBv element) (bvLit sortInfo.elements.size)
        let proof :=
          mkApp6 (mkConst ``Std.Tactic.BVDecide.EPR.BitVec.toBvAux_lt_ofNat_length_of_mem [sortInfo.level])
            sortInfo.type
            (toExpr width)
            elemList
            elemListLt
            element
            memProof
        facts := facts.push <| mkFact type proof
      if symBreak matches .simple | .full then
        let type ← Sym.share <| ← mkLE (mkApp toBv element) (bvLit idx)
        let proof :=
          mkApp8 (mkConst ``Std.Tactic.BVDecide.EPR.BitVec.toBvAux_le_ofNat_of_getElem_eq [sortInfo.level])
            sortInfo.type
            (toExpr width)
            elemList
            elemListLt
            element
            (toExpr idx)
            idxLt
            getElemEq
        facts := facts.push <| mkFact type proof
      if symBreak matches .full && idx != 0 then
        let thm :=
          mkApp8 (mkConst ``Std.Tactic.BVDecide.EPR.BitVec.toBvAux_ne_of_toBvAux_lt [sortInfo.level])
            sortInfo.type
            (toExpr width)
            elemList
            elemListLt
            element
            (toExpr idx)
            idxLt
            getElemEq
        let premise ← mkLt (mkApp toBv element) (bvLit idx)
        for k in (idx + 1)...sortInfo.card do
          let later := sortInfo.elements[k]!
          let conclusion := mkNot (mkApp3 (mkConst ``Eq [1]) (toTypeExpr (BitVec width)) (mkApp toBv later) (bvLit idx))
          let type ← Sym.share <| ← mkArrow premise conclusion
          facts := facts.push <| mkFact type (mkApp thm later)
    let sortInfo :=
      { sortInfo with width, toBv, elemList, elemListLt, elemListLength, elemListMemProofs, toSort }
    bvSortInfo := bvSortInfo.insert sortId sortInfo
  return (bvSortInfo, facts)

public def epr2BitVec (problem : EprProblem) (g : MVarId)
    (symBreak : Elab.Tactic.BVDecide.EprSymBreak) : Sym.SymM EprBvProblem := g.withContext do
  let (sortInfo, additionalFacts) ← translateSorts problem.sortInfo symBreak
  let predInfo ← translatePreds problem.predInfo sortInfo
  TranslateExprM.run { predInfo, sortInfo, sortMap := problem.sortMap } do
    let groundFacts ← problem.groundFacts.mapM translateGround
    let quantifiedFacts ← problem.quantifiedFacts.mapM translateQuantified
    return {
      sortInfo := sortInfo,
      sortMap := problem.sortMap
      predInfo := predInfo
      groundFacts := groundFacts ++ additionalFacts
      quantifiedFacts := quantifiedFacts
    }

end Lean.Meta.Tactic.BVDecide.EPR
