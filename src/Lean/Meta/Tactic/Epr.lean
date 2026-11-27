/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Basic
public import Std.Tactic.BVDecide.Syntax
import Lean.Meta.Sym.Simp.NNF
import Lean.Meta.Sym.Simp.Prenex
import Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps
import Lean.Meta.Tactic.BVDecide.Main
import Lean.Meta.Tactic.Grind.Main
public import Lean.Meta.Tactic.BVDecide.TacticContext
import Lean.Meta.Sym.Apply
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Intro
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Sym.SynthInstance
import Init.Sym.Lemmas
import Lean.Meta.Sym.Util

namespace Lean.Meta.Tactic

namespace Epr

open BVDecide Normalize

open Sym.Internal in
/--
Introduce `Nonempty` instances for as many type parameters as possible in the local context.
This is potentially useful for skolemization.
-/
def addNonempty (g : MVarId) : Sym.SymM Unit := do
  g.withContext do
    let mut todo : Std.HashSet FVarId := {}
    for decl in ← getLCtx do
      if decl.isImplementationDetail || decl.isLet then continue
      let type ← Sym.instantiateMVarsS decl.type
      if let .sort (.succ u) := type then
        let query ← mkAppS (← mkConstS ``Nonempty [.succ u]) (← Sym.share decl.toExpr)
        if (← Sym.synthInstance? query).isNone then
          todo := todo.insert decl.fvarId
      else if let .fvar typeId := type then
        if todo.contains typeId then
          let type ← mkFVarS typeId
          let lvl ← Sym.getLevel type
          let instType ← mkAppS (← mkConstS ``Nonempty [lvl]) type
          let inst ← mkAppS₂ (← mkConstS ``Nonempty.intro [lvl]) type (← Sym.share decl.toExpr)
          Sym.registerInstance instType inst
          todo := todo.erase typeId

/--
Convert all `hyps` to NNF.
-/
def nnf (hyps : Array Hyp) (cfg : BVDecide.TacticContext) : Sym.SymM (Array Hyp) :=
  let methods := { pre := Sym.Simp.nnf }
  Sym.Simp.SimpM.run' (methods := methods) (config := { maxSteps := cfg.config.maxSteps }) do
    hyps.mapM fun hyp => do
      let res ← Sym.Simp.simp hyp.type
      hyp.applySimpResult res

/--
Split up potential top level conjunctions in `hyps` and return them as multiple separate hypotheses.
-/
partial def andFlatten (hyps : Array Hyp) : Sym.SymM (Array Hyp) := do
  hyps.flatMapM fun hyp => flattenOne [hyp]
where
  flattenOne (worklist : List Hyp) (acc : Array Hyp := #[]) : Sym.SymM (Array Hyp) := do
    match worklist with
    | [] => return acc
    | hyp :: worklist =>
      match_expr hyp.type with
      | And lhs rhs =>
        let lhsHyp := {
          hyp with
            type := lhs,
            value := mkApp3 (mkConst ``And.left) lhs rhs hyp.value
            source := .andFlattened hyp.source
        }
        let rhsHyp := {
          hyp with
            type := rhs,
            value := mkApp3 (mkConst ``And.right) lhs rhs hyp.value
            source := .andFlattened hyp.source
        }
        flattenOne (lhsHyp :: rhsHyp :: worklist) acc
      | _ => flattenOne worklist (acc.push hyp)


/--
Prenxing formulas that contain exclusively universal quantifiers in positive polarity.
-/
def prenexForall (hyp : Hyp) (cfg : BVDecide.TacticContext) : Sym.SymM Hyp := do
  let cfg := { maxSteps := cfg.config.maxSteps }
  let hyp ← hyp.applySimpResult <| ← Sym.simp (methods := { pre := Sym.Simp.pullForall }) (config := cfg) hyp.type
  return hyp

structure SkolemCtx where
  universalFVars : Std.TreeMap FVarId Nat (Name.quickCmp ·.name ·.name) := {}
  depth : Nat := 0

structure SkolemState where
  skFnDecls : Array LocalDecl := #[]
  skFnValues : Array Expr := #[]
  skHypDecls : Array LocalDecl := #[]
  skHypProofs : Array Expr := #[]

def SkolemState.zip (sk : SkolemState) : Array (LocalDecl × Expr × LocalDecl × Expr) :=
  sk.skFnDecls.zip <| sk.skFnValues.zip <| sk.skHypDecls.zip <| sk.skHypProofs

abbrev SkolemM := ReaderT SkolemCtx StateRefT SkolemState Sym.SymM

-- Crucial: Returns an unshared expression with unregistered fvars
open Sym.Internal in
partial def extractSkolemFns (e : Expr) :
    Sym.SymM (Expr × Option Expr × SkolemState) := do
  let ((e, heq), state) ← go e |>.run {} |>.run {}
  return (e, heq, state)
where
  @[inline]
  isUniversalBinder (f : FVarId) : SkolemM Bool := do
    return (← read).universalFVars.contains f

  @[inline]
  withUniversalBinders {α : Type} (es : Array Expr) (x : SkolemM α) : SkolemM α := do
    let fvars := es.map Expr.fvarId!
    let mut universalFVars := (← read).universalFVars
    let mut depth := (← read).depth
    for fvar in fvars do
      universalFVars := universalFVars.insert fvar depth
      depth := depth + 1
    withReader (fun ctx => { ctx with universalFVars, depth }) do
      x

  registerSkolemFn (lvl : Level) (exType : Expr) (binderName? : Option Name) (eps : Expr) :
      SkolemM (Expr × Expr) := do
    let (_, epsFVars) ← eps.collectFVars |>.run {}
    let epsFVars ← epsFVars.fvarIds.filterM isUniversalBinder
    -- Sort by order of universal quantifier depth to avoid dependency issues
    let universalFVars := (← read).universalFVars
    let epsFVars := epsFVars.qsort fun l r => universalFVars[l]! < universalFVars[r]!
    let epsFVars := epsFVars.map mkFVar
    let skolemFn ← mkLambdaFVars epsFVars eps
    let skolemType ← mkForallFVars epsFVars exType
    let skolemFVar ← mkFreshFVarId
    -- index will be rewritten later by withExistingLocalDecls
    let skolemDecl := .cdecl 0 skolemFVar (binderName?.getD `sk) skolemType .default .default
    let skolemApp := mkAppN (mkFVar skolemFVar) epsFVars
    let skolemHypFVar ← mkFreshFVarId
    let skolemHypType ← mkForallFVars epsFVars <| mkApp3 (mkConst ``Eq [lvl]) exType eps skolemApp
    let skolemHypDecl := .cdecl 1 skolemHypFVar .anonymous skolemHypType .default .default
    let skolemHypProof ← mkLambdaFVars epsFVars <| mkApp2 (mkConst ``Eq.refl [lvl]) exType eps
    modify fun s => { s with
      skFnValues := s.skFnValues.push skolemFn
      skFnDecls := s.skFnDecls.push skolemDecl,
      skHypDecls := s.skHypDecls.push skolemHypDecl
      skHypProofs := s.skHypProofs.push skolemHypProof
    }
    let proof := mkAppN (mkFVar skolemHypFVar) epsFVars
    return (skolemApp, proof)

  mkPropCongr₂ (op lhs lhs' rhs rhs' : Expr) (lhsEq? rhsEq? : Option Expr) : Option Expr :=
    let prop := mkSort 0
    let propToProp := Lean.mkForall `a .default prop prop
    let congrOp (lhsEq : Expr) := mkApp6 (mkConst ``congrArg [1, 1]) prop propToProp lhs lhs' op lhsEq
    match lhsEq?, rhsEq? with
    | none, none => none
    | some lhsEq, none =>
      some <| mkApp6 (mkConst ``congrFun' [1, 1]) prop prop (mkApp op lhs) (mkApp op lhs') (congrOp lhsEq) rhs
    | none, some rhsEq =>
      some <| mkApp6 (mkConst ``congrArg [1, 1]) prop prop rhs rhs' (mkApp op lhs) rhsEq
    | some lhsEq, some rhsEq =>
      some <| mkApp8 (mkConst ``congr [1, 1]) prop prop (mkApp op lhs) (mkApp op lhs') rhs rhs'
        (congrOp lhsEq) rhsEq

  goBinary (e op lhs rhs : Expr) : SkolemM (Expr × Option Expr) := do
    let (lhs', lhsEq?) ← go lhs
    let (rhs', rhsEq?) ← go rhs
    if lhsEq?.isNone && rhsEq?.isNone then
      return (e, none)
    return (mkApp2 op lhs' rhs', mkPropCongr₂ op lhs lhs' rhs rhs' lhsEq? rhsEq?)

  /--
  Returns the skolemized `e'` together with a proof of `e = e'`, where `none` means `e' = e`.
  Proofs are built without type inference since terms may mention skolem fvars that are not in the
  local context yet.
  -/
  go (e : Expr) : SkolemM (Expr × Option Expr) := do
    match e with
    | .forallE n d b bi =>
      withLocalDecl n bi d fun x => do
        let (body', h?) ← withUniversalBinders #[x] do
          go (b.instantiate1 x)
        let some h := h? | return (e, none)
        let u ← getLevel d
        let q ← mkLambdaFVars #[x] body'
        let proof := mkApp4 (mkConst ``forall_congr [u]) d (.lam n d b bi) q (← mkLambdaFVars #[x] h)
        return (← mkForallFVars #[x] body', some proof)
    | _ =>
      match_expr e with
      | And lhs rhs => goBinary e (mkConst ``And) lhs rhs
      | Or lhs rhs => goBinary e (mkConst ``Or) lhs rhs
      | Exists α p =>
        let lvl ← getLevel α
        let some instNonempty ← Sym.synthInstance? (← mkAppS (← mkConstS ``Nonempty [lvl]) α)
          | throwError m!"Failed to skolemize at {e}, {α} is not `Nonempty`"
        let eps := mkApp3 (mkConst ``Classical.epsilon [lvl]) α instNonempty p
        let existsEqEps := mkApp3 (mkConst ``Sym.exists_eq_epsilon [lvl]) α instNonempty p
        let binderName? :=
          match p with
          | .lam binderName .. => some binderName
          | _ => none
        let (skolemApp, epsEqSkolem) ← registerSkolemFn lvl α binderName? eps
        let prop := mkSort 0
        let pEps := mkApp p eps
        let pSkolem := mkApp p skolemApp
        let pEpsEqPSkolem := mkApp6 (mkConst ``congrArg [lvl, 1]) α prop eps skolemApp p epsEqSkolem
        let eEqPSkolem := mkApp6 (mkConst ``Eq.trans [1]) prop e pEps pSkolem existsEqEps pEpsEqPSkolem
        let (p', pEq?) ← go (p.beta #[skolemApp])
        let some pEq := pEq? | return (p', some eEqPSkolem)
        return (p', some <| mkApp6 (mkConst ``Eq.trans [1]) prop e pSkolem p' eEqPSkolem pEq)
      | _ => return (e, none)

open Sym.Internal in
def skolemize (g : MVarId) (hyp : Hyp) (cfg : BVDecide.TacticContext) :
    Sym.SymM (MVarId × Hyp) := do
  let hyp ← prepareSkolemize hyp
  let (newHypType, hypEq?, skState) ← extractSkolemFns hyp.type
  let allDecls := skState.skFnDecls ++ skState.skHypDecls |>.toList
  g.withContext do
  withExistingLocalDecls allDecls do
    let newGoal ← mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
    let mut gProof := newGoal
    for (skDecl, skValue, skHypDecl, skHypProof) in skState.zip.reverse do
      gProof := mkApp2 (← mkLambdaFVars #[skDecl.toExpr, skHypDecl.toExpr] gProof) skValue skHypProof
    g.assign gProof
    let newGoal ← Sym.preprocessMVar newGoal.mvarId!
    newGoal.withContext do
      -- newHypType previously refers to fvars that are not yet in the lctx
      let newHypType ← Sym.shareCommon newHypType
      let proof :=
        match hypEq? with
        | none => hyp.value
        | some hypEq => mkApp4 (mkConst ``Eq.mp [0]) hyp.type newHypType hypEq hyp.value
      let hyp := { hyp with type := newHypType, value := proof }
      return (newGoal, hyp)
where
  prepareSkolemize (hyp : Hyp) : Sym.SymM Hyp := do
    let cfg := { maxSteps := cfg.config.maxSteps }
    -- minscope to remove universal if possible
    let hyp ← hyp.applySimpResult <| ← Sym.simp (methods := { pre := Sym.Simp.minscope }) (config := cfg) hyp.type
    -- pull existentials to reuse skolem functions if possible
    let hyp ← hyp.applySimpResult <| ← Sym.simp (methods := { pre := Sym.Simp.pullExists }) (config := cfg) hyp.type
    return hyp

end Epr

public def epr (g : MVarId) (cfg : BVDecide.TacticContext) : MetaM Unit := g.withContext do
  let params ← Grind.mkDefaultParams {}
  Grind.GrindM.run (params := params) do
    let (hyps, g) ← BVDecide.Normalize.collectMVarHyps g
    Epr.addNonempty g
    g.withContext do
      let hyps ← Epr.nnf hyps cfg
      let hyps ← Epr.andFlatten hyps
      let mut finalHyps := Array.emptyWithCapacity hyps.size
      let mut g := g
      for hyp in hyps do
        let mut hyp := hyp
        if hyp.type.find? (fun e => e.isConstOf ``Exists) |>.isSome then
          let (g', hyp') ← g.withContext do Epr.skolemize g hyp cfg
          g := g'
          hyp := hyp'
        hyp ← g.withContext do
          Epr.prenexForall hyp cfg
        finalHyps := finalHyps.push hyp
      let target := .hypTarget g finalHyps
      discard <| BVDecide.bvDecide target cfg

end Lean.Meta.Tactic
