/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.ApplyControlFlow
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Structures
import Lean.Meta.Tactic.Simp

/-!
This module contains the implementation of the pre processing pass for handling enum inductive
types.

The implementation:
1. generates mappings from enum inductives occuring in the goal to sufficiently large `BitVec` and
   replaces equality on the enum inductives with equality on these mapping functions.
2. Constant folds these mappings if appropriate.
3. Adds bounds on the values returned by the mappings if the size of the enum inductive does not fit
   into a power of two.
4. Handles applications of these mappings to `ite`, `cond` and basic match statements.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

private def getBitVecSize (domainSize : Nat) : Nat :=
  let bvSize := Nat.log2 domainSize
  if 2^bvSize == domainSize then
    bvSize
  else
    bvSize + 1

def enumToBitVecSuffix : String := "enumToBitVec"
def eqIffEnumToBitVecEqSuffix : String := "eq_iff_enumToBitVec_eq"
def enumToBitVecLeSuffix : String := "enumToBitVec_le"
def matchEqCondSuffix : String := "eq_cond_enumToBitVec"

/--
Assuming that `declName` is an enum inductive construct a function of type `declName → BitVec w`
that maps `declName` constructors to their numeric indices as `BitVec`.
-/
def getEnumToBitVecFor (declName : Name) : MetaM Name := do
  let enumToBitVecName := Name.str declName enumToBitVecSuffix
  realizeConst declName enumToBitVecName do
    let env ← getEnv
    let .inductInfo inductiveInfo ← getConstInfo declName | throwError m!"{declName} is not an inductive."
    if !(← isEnumType declName) then
      throwError m!"{declName} is not an enum inductive."
    let domainSize := inductiveInfo.ctors.length
    let bvSize := getBitVecSize domainSize
    let bvType := mkApp (mkConst ``BitVec) (toExpr bvSize)
    let declType := mkConst declName
    let translator ←
      withLocalDeclD `x declType fun x => do
        let motive := mkLambda .anonymous .default declType bvType
        let recOn := mkApp2 (mkConst (mkRecOnName declName) [1]) motive x
        let translator :=
          Nat.fold
            domainSize
            (init := recOn)
            (fun i _ acc => mkApp acc <| toExpr <| BitVec.ofNat bvSize i)
        mkLambdaFVars #[x] translator
    addDecl <| .defnDecl {
      name := enumToBitVecName
      type := (← mkArrow declType bvType)
      levelParams := []
      value := translator
      hints := .regular (getMaxHeight env translator + 1)
      safety := .safe
    }
  return enumToBitVecName

/--
Create a `cond` chain in `Sort u` of the form:
```
bif input = 0#w then values[0] else bif input = 1#w then values[1] else ...
```
-/
private def mkCondChain (u : Level) (w : Nat) (input : Expr) (retType : Expr) (values : List Expr)
    (acc : Expr) : MetaM Expr := do
  let instBEq ← synthInstance (mkApp (mkConst ``BEq [0]) (mkApp (mkConst ``BitVec) (toExpr w)))
  return go u input retType instBEq values (BitVec.ofNat w 0) acc
where
  go {w : Nat} (u : Level) (input : Expr) (retType : Expr) (instBEq : Expr) (values : List Expr)
    (counter : BitVec w) (acc : Expr) : Expr :=
  match values with
  | [] => acc
  | value :: values =>
    let eq :=
      mkApp4
        (mkConst ``BEq.beq [0])
        (toTypeExpr <| BitVec w)
        instBEq
        input
        (toExpr counter)
    let acc := mkApp4 (mkConst ``cond [u]) retType eq value acc
    go u input retType instBEq values (counter + 1) acc

/--
Build `declName.recOn.{0} (motive := motive) value (f context[0]) (f context[1]) ...`
-/
private def enumCases (declName : Name) (motive : Expr) (value : Expr) (context : List α)
    (f : α → MetaM Expr) : MetaM Expr := do
  let recOn := mkApp2 (mkConst (mkRecOnName declName) [0]) motive value
  List.foldlM (init := recOn) (fun acc a => mkApp acc <$> f a) context

/--
Assuming that `declName` is an enum inductive, construct a proof of
`∀ (x y : declName) : x = y ↔ x.enumToBitVec = y.enumToBitVec`.
-/
def getEqIffEnumToBitVecEqFor (declName : Name) : MetaM Name := do
  let eqIffEnumToBitVecEqName := Name.str declName eqIffEnumToBitVecEqSuffix
  realizeConst declName eqIffEnumToBitVecEqName do
    /-
    We prove the lemma by constructing an inverse to `enumToBitVec` and use the fact that all
    invertible functions respect equality.
    -/
    let enumToBitVec := mkConst (← getEnumToBitVecFor declName)
    let .inductInfo inductiveInfo ← getConstInfo declName | unreachable!
    let ctors := inductiveInfo.ctors
    let domainSize := ctors.length
    let bvSize := getBitVecSize domainSize
    let bvType := mkApp (mkConst ``BitVec) (toExpr bvSize)
    let declType := mkConst declName

    -- ∀ (x y : declName), x = y ↔ enumToBitVec x = enumToBitVec y
    let type ←
      withLocalDeclD `x declType fun x =>
      withLocalDeclD `y declType fun y => do
        let lhs := mkApp3 (mkConst ``Eq [1]) declType x y
        let rhs :=
          mkApp3
            (mkConst ``Eq [1])
            bvType
            (mkApp enumToBitVec x)
            (mkApp enumToBitVec y)
        let statement := mkApp2 (mkConst ``Iff) lhs rhs

        mkForallFVars #[x, y] statement

    -- the inverse of enumToBitVec
    let inverseValue ←
      withLocalDeclD `x bvType fun x => do
        let ctors := ctors.map mkConst
        let inv ← mkCondChain 1 bvSize x declType ctors ctors.head!
        mkLambdaFVars #[x] inv

    let value ←
      withLetDecl `inverse (← mkArrow bvType declType) inverseValue fun inv => do
        let invProof ←
          withLocalDeclD `x declType fun x => do
            let toBvToEnum e := mkApp inv (mkApp enumToBitVec e)
            let motive ←
              withLocalDeclD `y declType fun y =>
                mkLambdaFVars #[y] <| mkApp3 (mkConst ``Eq [1]) declType (toBvToEnum y) y

            let case ctor := do
              return mkApp2 (mkConst ``Eq.refl [1]) declType (toBvToEnum (mkConst ctor))
            let proof ← enumCases declName motive x ctors case
            mkLambdaFVars #[x] proof

        let value :=
          mkApp5
            (mkConst ``BitVec.eq_iff_eq_of_inv [1])
            declType
            (toExpr bvSize)
            enumToBitVec
            inv
            invProof
        mkLetFVars #[inv] value

    addDecl <| .thmDecl {
      name := eqIffEnumToBitVecEqName
      levelParams := []
      type := type
      value := value
    }
  return eqIffEnumToBitVecEqName

/--
Assuming that `declName` is an enum inductive, construct a proof of
`∀ (x : declName) : x.enumToBitVec ≤ domainSize - 1` where `domainSize` is the amount of
constructors of `declName`.
-/
def getEnumToBitVecLeFor (declName : Name) : MetaM Name := do
  let enumToBitVecLeName := Name.str declName enumToBitVecLeSuffix
  realizeConst declName enumToBitVecLeName do
    let enumToBitVec := mkConst (← getEnumToBitVecFor declName)
    let .inductInfo inductiveInfo ← getConstInfo declName | unreachable!
    let ctors := inductiveInfo.ctors
    let domainSize := ctors.length
    let bvSize := getBitVecSize domainSize
    let bvType := mkApp (mkConst ``BitVec) (toExpr bvSize)
    let declType := mkConst declName
    let maxValue := toExpr (BitVec.ofNat bvSize (domainSize - 1))
    let instLe ← synthInstance (mkApp (mkConst ``LE [0]) bvType)
    let mkStatement e := mkApp4 (mkConst ``LE.le [0]) bvType instLe (mkApp enumToBitVec e) maxValue

    -- ∀ (x : declName), enumToBitVec x ≤ BitVec.ofNat bvSize (domainSize - 1)
    let (type, value) ←
      withLocalDeclD `x declType fun x => do
        let statement := mkStatement x
        let motive ← mkLambdaFVars #[x] statement
        let case ctor := do
          let statement := mkStatement (mkConst ctor)
          mkDecideProof statement
        let cases ← enumCases declName motive x ctors case
        return (← mkForallFVars #[x] statement, ← mkLambdaFVars #[x] cases)

    addDecl <| .thmDecl {
      name := enumToBitVecLeName
      levelParams := []
      type := type
      value := value
    }
  return enumToBitVecLeName

/--
Generate a theorem that translates `.match_x` applications on enum inductives to chains of `cond`,
assuming that it is a supported kind of match, see `matchIsSupported` for the currently available
variants.
-/
private def getMatchEqCondForAux (declName : Name) (kind : MatchKind) : MetaM Name := do
  let matchEqCondName := .str declName matchEqCondSuffix
  realizeConst declName matchEqCondName do
    let decl ←
      match kind with
      | .simpleEnum inductiveInfo => handleSimpleEnum declName matchEqCondName inductiveInfo
    addDecl decl
  return matchEqCondName
where
  handleSimpleEnum (declName : Name) (thmName : Name) (inductiveInfo : InductiveVal) :
      MetaM Declaration := do
    let uName ← mkFreshUserName `u
    let u := .param uName
    let (type, value) ←
      withLocalDeclD `a (.sort u) fun a => do
      withLocalDeclD `x (mkConst inductiveInfo.name) fun x => do
        let hType ← mkArrow (mkConst ``Unit) a
        let hBinders := inductiveInfo.ctors.foldl (init := #[]) (fun acc _ => acc.push (`h, hType))
        withLocalDeclsDND hBinders fun hs => do
          let args := #[mkLambda `x .default (mkConst inductiveInfo.name) a , x] ++ hs
          let lhs := mkAppN (mkConst declName [u]) args
          let enumToBitVec := mkConst (← getEnumToBitVecFor inductiveInfo.name)
          let domainSize := inductiveInfo.ctors.length
          let bvSize := getBitVecSize domainSize
          let appliedHs := hs.toList.map (mkApp · (mkConst ``Unit.unit))
          let rhs ← mkCondChain u bvSize (mkApp enumToBitVec x) a appliedHs appliedHs[0]!
          let type := mkApp3 (mkConst ``Eq [u]) a lhs rhs

          let motive ← mkLambdaFVars #[x] type
          let case h := do
            return mkApp2 (mkConst ``Eq.refl [u]) a (mkApp h (mkConst ``Unit.unit))
          let cases ← enumCases inductiveInfo.name motive x hs.toList case

          let fvars := #[a, x] ++ hs
          return (← mkForallFVars fvars type, ← mkLambdaFVars fvars cases)

    return .thmDecl {
      name := thmName
      levelParams := [uName]
      type := type
      value := value
    }

/--
Obtain a theorem that translates `.match_x` applications on enum inductives to chains of `cond`
applications. If the specific `.match_x` that this is being called on is unsupported throw an error.
-/
def getMatchEqCondFor (declName : Name) : MetaM Name := do
  if let some kind ← isSupportedMatch declName then
    return (← getMatchEqCondForAux declName kind)
  else
    throwError m!"{matchEqCondSuffix} lemma could not be established for {declName}"

builtin_initialize
  registerReservedNamePredicate fun env name => Id.run do
    let .str p s := name | return false
    s == enumToBitVecSuffix || s == eqIffEnumToBitVecEqSuffix || s == enumToBitVecLeSuffix ||
    (s == matchEqCondSuffix && isMatcherCore env p)

builtin_initialize
  registerReservedNameAction fun name => do
    let .str p s := name | return false
    if ← isEnumType p then
      if s == enumToBitVecSuffix then
        discard <| MetaM.run' (getEnumToBitVecFor p)
        return true
      else if s == eqIffEnumToBitVecEqSuffix then
        discard <| MetaM.run' (getEqIffEnumToBitVecEqFor p)
        return true
      else if s == enumToBitVecLeSuffix then
        discard <| MetaM.run' (getEnumToBitVecLeFor p)
        return true
      else
        return false
    else if (s == matchEqCondSuffix && (← isMatcher p)) then
      discard <| MetaM.run' (getMatchEqCondFor p)
      return true
    else
      return false

/--
This simproc should be set up to trigger on expressions of the form `EnumInductive.enumToBitVec x`.
It will check if `x` is a constructor and if that is the case constant fold it to the corresponding
`BitVec` value.
-/
def enumToBitVecCtor : Simp.Simproc := fun e => do
  let .app (.const fn []) (.const arg []) := e | return .continue
  let .str p s := fn | return .continue
  if s != enumToBitVecSuffix then return .continue
  if !(← isEnumType p) then return .continue
  let .inductInfo inductiveInfo ← getConstInfo p | unreachable!
  let ctors := inductiveInfo.ctors
  let some ctorIdx := ctors.findIdx? (· == arg) | return .continue
  let bvSize := getBitVecSize ctors.length
  return .done { expr := toExpr <| BitVec.ofNat bvSize ctorIdx }

/--
The state used for the post processing part of `enumsPass`.
-/
private structure PostProcessState where
  /--
  Hypotheses that bound results of `enumToBitVec` applications as appropriate.
  -/
  hyps : Array Hypothesis := #[]
  /--
  A cache of terms we have already collected bounds for such that they don't get duplicated.
  -/
  seen : Std.HashSet Expr := {}

partial def enumsPass : Pass where
  name := `enums
  run' goal :=
    goal.withContext do
      let analysis ← PreProcessM.getTypeAnalysis
      let interestingEnums := analysis.interestingEnums
      -- invariant: if there is no interesting enums there also can't be interesting matchers
      if interestingEnums.isEmpty then return goal

      let mut simprocs : Simprocs := {}
      let mut relevantLemmas : SimpTheoremsArray := #[]
      relevantLemmas ← relevantLemmas.addTheorem (.decl ``ne_eq) (mkConst ``ne_eq)
      for type in interestingEnums do
        let lemma ← getEqIffEnumToBitVecEqFor type
        relevantLemmas ← relevantLemmas.addTheorem (.decl lemma) (mkConst lemma)

        let enumToBitVec ← getEnumToBitVecFor type
        let path := #[.const enumToBitVec 1, .star]
        simprocs := simprocs.addCore path ``enumToBitVecCtor true (.inl enumToBitVecCtor)

        let path := mkApplyUnaryControlDiscrPath type 0 enumToBitVec ``ite 5
        simprocs := simprocs.addCore path ``applyIteSimproc false (.inl applyIteSimproc)
        let path := mkApplyUnaryControlDiscrPath type 0 enumToBitVec ``cond 4
        simprocs := simprocs.addCore path ``applyCondSimproc false (.inl applyCondSimproc)

      let interestingMatchers := analysis.interestingMatchers
      for (matcher, kind) in interestingMatchers do
        let lemma ← getMatchEqCondForAux matcher kind
        relevantLemmas ← relevantLemmas.addTheorem (.decl lemma) (mkConst lemma)

      -- Desugaring matches could have potentially revealed new opportunities to do stuff with
      -- structures. Thus we must also re run lemmas that handle structure projections in the
      -- presence of control flow.
      let cfg ← PreProcessM.getConfig
      if cfg.structures then
        (simprocs, relevantLemmas) ← addStructureSimpLemmas simprocs relevantLemmas

      let simpCtx ← Simp.mkContext
        (config := { failIfUnchanged := false, maxSteps := cfg.maxSteps })
        (simpTheorems := relevantLemmas)
        (congrTheorems := ← getSimpCongrTheorems)

      let ⟨result?, _⟩ ←
        simpGoal
          goal
          (ctx := simpCtx)
          (simprocs := #[simprocs])
          (fvarIdsToSimp := ← getPropHyps)
      let some (_, newGoal) := result? | return none
      postprocess newGoal |>.run' {}
where
  postprocess (goal : MVarId) : StateRefT PostProcessState MetaM MVarId :=
    goal.withContext do
      let filter e :=
        if let .app (.const (.str _ s) []) _ := e then
          s == enumToBitVecSuffix
        else
          false

      let processor e := do
        /-
        It is important that we maintain our own cache here in addition to the one of
        `forEachWhere`. This is because we call `forEachWhere` on multiple hypotheses and two
        hypotheses could contain the same term but we still do not wan't to duplicate bounds
        hypotheses for it.
        -/
        if (← get).seen.contains e then return ()
        let .app (.const (.str enumType _) []) val := e | unreachable!
        let lemma := mkConst (← getEnumToBitVecLeFor enumType)
        let value := mkApp lemma val
        let type ← inferType value
        let hyp := { userName := .anonymous, type, value }
        modify fun s => { s with hyps := s.hyps.push hyp, seen := s.seen.insert e }

      for hyp in ← getPropHyps do
        (← instantiateMVars (← hyp.getType)).forEachWhere (stopWhenVisited := true) filter processor

      let newHyps := (← get).hyps
      if newHyps.isEmpty then
        return goal
      else
        let (_, goal) ← goal.assertHypotheses newHyps
        return goal

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
