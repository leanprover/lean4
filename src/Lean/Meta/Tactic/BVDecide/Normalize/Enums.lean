/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Structures
import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow
import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Util
import Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec
import Init.Data.Nat.Power2.Bitwise


/-!
This module contains the implementation of the pre processing pass for handling enum inductive
types.

The implementation:
1. generates mappings from enum inductives occurring in the goal to sufficiently large `BitVec` and
   replaces equality on the enum inductives with equality on these mapping functions.
2. Constant folds these mappings if appropriate.
3. Adds bounds on the values returned by the mappings if the size of the enum inductive does not fit
   into a power of two.
4. Handles applications of these mappings to `ite`, `cond` and basic match statements.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

def getBitVecSize (domainSize : Nat) : Nat :=
  let bvSize := Nat.log2 domainSize
  if 2^bvSize == domainSize then
    bvSize
  else
    bvSize + 1

public def enumToBitVecSuffix : String := "enumToBitVec"
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
    let .inductInfo inductiveInfo ← getConstInfo declName | throwError m!"{.ofConstName declName} is not an inductive."
    if !(← isEnumType declName) then
      throwError m!"{.ofConstName declName} is not an enum inductive."
    let domainSize := inductiveInfo.ctors.length
    let bvSize := getBitVecSize domainSize
    let bvType := mkApp (mkConst ``BitVec) (toExpr bvSize)
    let levelParamNames := inductiveInfo.levelParams
    let levelParams := inductiveInfo.levelParams.map mkLevelParam
    let declType := mkConst declName levelParams
    let translator ←
      withLocalDeclD `x declType fun x => do
        let motive := mkLambda .anonymous .default declType bvType
        let recOn := mkApp2 (mkConst (mkRecOnName declName) (1 :: levelParams)) motive x
        let translator :=
          Nat.fold
            domainSize
            (init := recOn)
            (fun i _ acc => mkApp acc <| toExpr <| BitVec.ofNat bvSize i)
        mkLambdaFVars #[x] translator
    addDecl <| .defnDecl {
      name := enumToBitVecName
      type := (← mkArrow declType bvType)
      levelParams := levelParamNames
      value := translator
      hints := .regular (getMaxHeight env translator + 1)
      safety := .safe
    }
  return enumToBitVecName

/--
Create a `cond` chain in `Sort u` of the form:
```
bif input = discrs 0 then values[0] else bif input = discrs 1 then values 1 else ...
```
-/
private def mkCondChain {w : Nat} (input : Expr) (retType : Expr)
    (discrs : Nat → BitVec w) (values : List Expr) (acc : Expr) : MetaM Expr := do
  let instBEq ← synthInstance (mkApp (mkConst ``BEq [0]) (toTypeExpr <| BitVec w))
  go input retType instBEq discrs values 0 acc
where
  go {w : Nat} (input : Expr) (retType : Expr) (instBEq : Expr)
    (discrs : Nat → BitVec w) (values : List Expr) (counter : Nat) (acc : Expr) : MetaM Expr := do
  match values with
  | [] => return acc
  | value :: values =>
    let eq :=
      mkApp4
        (mkConst ``BEq.beq [0])
        (toTypeExpr <| BitVec w)
        instBEq
        input
        (toExpr <| discrs counter)
    let acc ← mkAppM ``cond #[eq, value, acc]
    go input retType instBEq discrs values (counter + 1) acc

/--
Build `declName.recOn.{0} (motive := motive) value (f context[0]) (f context[1]) ...`
-/
private def enumCases (declName : Name) (motive : Expr)
    (value : Expr) (context : List α) (f : α → MetaM Expr) : MetaM Expr := do
  let args ← context.toArray.mapM (fun c => do return some (← f c))
  mkAppOptM (mkRecOnName declName) (#[some motive, some value] ++ args)

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
    let .inductInfo inductiveInfo ← getConstInfo declName | unreachable!
    let levelParamNames := inductiveInfo.levelParams
    let levelParams := inductiveInfo.levelParams.map mkLevelParam
    let enumToBitVec := mkConst (← getEnumToBitVecFor declName) levelParams
    let ctors := inductiveInfo.ctors
    let domainSize := ctors.length
    let bvSize := getBitVecSize domainSize
    let bvType := mkApp (mkConst ``BitVec) (toExpr bvSize)
    let declType := mkConst declName levelParams

    -- ∀ (x y : declName), x = y ↔ enumToBitVec x = enumToBitVec y
    let type ←
      withLocalDeclD `x declType fun x =>
      withLocalDeclD `y declType fun y => do
        let lhs ← mkEq x y
        let rhs ← mkEq (mkApp enumToBitVec x) (mkApp enumToBitVec y)
        let statement := mkApp2 (mkConst ``Iff) lhs rhs

        mkForallFVars #[x, y] statement

    -- the inverse of enumToBitVec
    let inverseValue ←
      withLocalDeclD `x bvType fun x => do
        let ctors := ctors.map (mkConst · levelParams)
        let inv ← mkCondChain x declType (BitVec.ofNat bvSize) ctors ctors.head!
        mkLambdaFVars #[x] inv

    let value ←
      withLetDecl `inverse (← mkArrow bvType declType) inverseValue fun inv => do
        let invProof ←
          withLocalDeclD `x declType fun x => do
            let toBvToEnum e := mkApp inv (mkApp enumToBitVec e)
            let motive ←
              withLocalDeclD `y declType fun y => do
                mkLambdaFVars #[y] (← mkEq (toBvToEnum y) y)

            let case ctor := mkEqRefl (toBvToEnum (mkConst ctor levelParams))
            let proof ← enumCases declName motive x ctors case
            mkLambdaFVars #[x] proof

        let value ← mkAppM ``BitVec.eq_iff_eq_of_inv #[enumToBitVec, inv, invProof]
        mkLetFVars #[inv] value

    addDecl <| .thmDecl {
      name := eqIffEnumToBitVecEqName
      levelParams := levelParamNames
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
    let .inductInfo inductiveInfo ← getConstInfo declName | unreachable!
    let levelParamNames := inductiveInfo.levelParams
    let levelParams := inductiveInfo.levelParams.map mkLevelParam
    let enumToBitVec := mkConst (← getEnumToBitVecFor declName) levelParams
    let ctors := inductiveInfo.ctors
    let domainSize := ctors.length
    let bvSize := getBitVecSize domainSize
    let bvType := mkApp (mkConst ``BitVec) (toExpr bvSize)
    let declType := mkConst declName levelParams
    let maxValue := toExpr (BitVec.ofNat bvSize (domainSize - 1))
    let instLe ← synthInstance (mkApp (mkConst ``LE [0]) bvType)
    let mkStatement e := mkApp4 (mkConst ``LE.le [0]) bvType instLe (mkApp enumToBitVec e) maxValue

    -- ∀ (x : declName), enumToBitVec x ≤ BitVec.ofNat bvSize (domainSize - 1)
    let (type, value) ←
      withLocalDeclD `x declType fun x => do
        let statement := mkStatement x
        let motive ← mkLambdaFVars #[x] statement
        let case ctor := do
          let statement := mkStatement (mkConst ctor levelParams)
          mkDecideProof statement
        let cases ← enumCases declName motive x ctors case
        return (← mkForallFVars #[x] statement, ← mkLambdaFVars #[x] cases)

    addDecl <| .thmDecl {
      name := enumToBitVecLeName
      levelParams := levelParamNames
      type := type
      value := value
    }
  return enumToBitVecLeName

/--
Generate a theorem that translates `.match_x` applications on enum inductives to chains of `cond`,
assuming that it is a supported kind of match, see `matchIsSupported` for the currently available
variants.
-/
private partial def getMatchEqCondForAux (declName : Name) (kind : MatchKind) : MetaM Name := do
  let matchEqCondName := .str declName matchEqCondSuffix
  realizeConst declName matchEqCondName do
    let decl ←
      match kind with
      | .simpleEnum inductiveInfo ctors =>
        handleSimpleEnum declName matchEqCondName inductiveInfo ctors
      | .enumWithDefault inductiveInfo ctors =>
        handleEnumWithDefault declName matchEqCondName inductiveInfo ctors
    addDecl decl
  return matchEqCondName
where
  handleSimpleEnum (declName : Name) (thmName : Name) (inductiveInfo : InductiveVal)
      (ctors : Array ConstructorVal) : MetaM Declaration := do
    let matchConstInfo ← getConstInfo declName
    let levelParamNames := matchConstInfo.levelParams
    let u := mkLevelParam levelParamNames.getLast!
    let levelParams := levelParamNames.map mkLevelParam
    let .forallE _ (.forallE _ discrType ..) .. := matchConstInfo.type | unreachable!
    let (type, value) ←
      withLocalDeclD `a (.sort u) fun a => do
      withLocalDeclD `x discrType  fun x => do
        let hType ← mkArrow (mkConst ``Unit) a
        let hBinders := ctors.foldl (init := #[]) (fun acc _ => acc.push (`h, hType))
        withLocalDeclsDND hBinders fun hs => do
          let args := #[mkLambda `x .default discrType a , x] ++ hs
          let lhs := mkAppN (mkConst declName levelParams) args
          let enumToBitVec ← getEnumToBitVecFor inductiveInfo.name
          let domainSize := inductiveInfo.ctors.length
          let bvSize := getBitVecSize domainSize
          let appliedHs := hs.toList.map (mkApp · (mkConst ``Unit.unit))
          let getBitVec i := BitVec.ofNat bvSize ctors[i]!.cidx
          let rhs ← mkCondChain (← mkAppM enumToBitVec #[x]) a getBitVec appliedHs appliedHs[0]!
          let type ← mkEq lhs rhs
          let motive ← mkLambdaFVars #[x] type
          let sortedHs :=
            hs
             |>.mapIdx (fun i h => (ctors[i]!.cidx, h))
             |>.qsort (·.1 < ·.1)
          let case h := mkEqRefl (mkApp h.2 (mkConst ``Unit.unit))
          let cases ← enumCases inductiveInfo.name motive x sortedHs.toList case

          let fvars := #[a, x] ++ hs
          return (← mkForallFVars fvars type, ← mkLambdaFVars fvars cases)

    return .thmDecl {
      name := thmName
      levelParams := levelParamNames
      type := type
      value := value
    }

  handleEnumWithDefault (declName : Name) (thmName : Name) (inductiveInfo : InductiveVal)
      (ctors : Array ConstructorVal) : MetaM Declaration := do
    let matchConstInfo ← getConstInfo declName
    let levelParamNames := matchConstInfo.levelParams
    let u := mkLevelParam levelParamNames.getLast!
    let levelParams := levelParamNames.map mkLevelParam
    let .forallE _ (.forallE _ discrType ..) .. := matchConstInfo.type | unreachable!
    let (type, value) ←
      withLocalDeclD `a (.sort u) fun a => do
      withLocalDeclD `x discrType fun x => do
        let hType ← mkArrow (mkConst ``Unit) a
        let mut hBinders := ctors.foldl (init := #[]) (fun acc _ => acc.push (`h, hType))
        hBinders := hBinders.push <| (`h, ← mkArrow discrType a)
        withLocalDeclsDND hBinders fun hs => do
          let args := #[mkLambda `x .default discrType a , x] ++ hs
          let lhs := mkAppN (mkConst declName levelParams) args
          let enumToBitVec ← getEnumToBitVecFor inductiveInfo.name
          let domainSize := inductiveInfo.ctors.length
          let bvSize := getBitVecSize domainSize
          let hdefault := hs.back!
          let concrete := hs.take <| hs.size - 1
          let appliedDefault := mkApp hdefault x
          let appliedConcrete := concrete.toList.map (mkApp · (mkConst ``Unit.unit))
          let getBitVec i := BitVec.ofNat bvSize ctors[i]!.cidx
          let rhs ← mkCondChain (← mkAppM enumToBitVec #[x]) a getBitVec appliedConcrete appliedDefault
          let type ← mkEq lhs rhs
          let motive ← mkLambdaFVars #[x] type
          let sortedConcreteHs :=
            concrete
             |>.mapIdx (fun i h => (ctors[i]!.cidx, h))
             |>.qsort (·.1 < ·.1)
             |>.toList

          let discrParams := discrType.constLevels!
          let rec intersperseDefault hs idx acc := do
            if idx == inductiveInfo.numCtors then
              return acc.reverse
            else
              match hs with
              | [] =>
                let ctor := mkConst inductiveInfo.ctors[idx]! discrParams
                let new := (idx, mkApp hdefault ctor)
                intersperseDefault hs (idx + 1) (new :: acc)
              | hs@((cidx, h) :: tail) =>
                if cidx == idx then
                  let new := (idx, mkApp h (mkConst ``Unit.unit))
                  intersperseDefault tail (idx + 1) (new :: acc)
                else
                  let ctor := mkConst inductiveInfo.ctors[idx]! discrParams
                  let new := (idx, mkApp hdefault ctor)
                  intersperseDefault hs (idx + 1) (new :: acc)

          let caseProofs ← intersperseDefault sortedConcreteHs 0 []
          let case h := mkEqRefl h.2
          let cases ← enumCases inductiveInfo.name motive x caseProofs case

          let fvars := #[a, x] ++ hs
          return (← mkForallFVars fvars type, ← mkLambdaFVars fvars cases)

    return .thmDecl {
      name := thmName
      levelParams := levelParamNames
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
    throwError m!"{matchEqCondSuffix} lemma could not be established for {.ofConstName declName}"

builtin_initialize
  registerReservedNamePredicate fun env name => Id.run do
    let .str p s := name | return false
    s == enumToBitVecSuffix || s == eqIffEnumToBitVecEqSuffix || s == enumToBitVecLeSuffix ||
    (s == matchEqCondSuffix && isMatcherCore env p)

builtin_initialize
  registerReservedNameAction fun name => do
    let .str p s := name | return false
    unless s == enumToBitVecSuffix ||
           s == eqIffEnumToBitVecEqSuffix ||
           s == enumToBitVecLeSuffix do return false
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
def enumToBitVecCtor : Sym.Simp.Simproc := fun e => do
  let .app (.const fn ..) (.const arg ..) := e | return .rfl
  let .str p s := fn | return .rfl
  if s != enumToBitVecSuffix then return .rfl
  if !(← isEnumType p) then return .rfl
  let .inductInfo inductiveInfo ← getConstInfo p | unreachable!
  let ctors := inductiveInfo.ctors
  let some ctorIdx := ctors.findIdx? (· == arg) | return .rfl
  let bvSize := getBitVecSize ctors.length
  let groundExpr ← Sym.share <| toExpr <| BitVec.ofNat bvSize ctorIdx
  let proof ← mkEqRefl groundExpr
  return .step groundExpr proof (done := true)

structure EnumInfo where
  toBitVec : Name
  toBitVecLemma : Name

def enumEqToBitVecEq (index : Std.HashMap Name EnumInfo) : Sym.Simp.Simproc := fun e => do
  let_expr Eq α lhs rhs := e | return .rfl
  let .const type _ := α.getAppFn' | return .rfl
  let some info := index[type]? | return .rfl
  let lhsBv ← mkAppM info.toBitVec #[lhs]
  let rhsBv ← mkAppM info.toBitVec #[rhs]
  let expr' ← mkEq lhsBv rhsBv
  let proof ← mkPropExt (← mkAppM info.toBitVecLemma #[lhs, rhs])
  return .step (← Sym.share expr') proof

/--
The state used for the post processing part of `enumsPass`.
-/
private structure PostProcessState where
  /--
  A cache of terms we have already collected bounds for such that they don't get duplicated.
  -/
  seen : Std.HashSet Sym.ExprPtr := {}

public partial def enumsPass : Pass where
  name := `enums
  run' := do
    let goal ← PreProcessM.getTargetMVarId
    goal.withContext do
      let analysis ← PreProcessM.getTypeAnalysis
      let interestingEnums := analysis.interestingEnums
      -- invariant: if there is no interesting enums there also can't be interesting matchers
      if interestingEnums.isEmpty then return false

      let mut methods := {}
      let mut relevantLemmas : Sym.Simp.Theorems := {}
      let mut toBitVecFns := {}
      let mut enumIndex := {}
      for type in interestingEnums do
        let lemma ← getEqIffEnumToBitVecEqFor type
        let enumToBitVec ← getEnumToBitVecFor type
        enumIndex := enumIndex.insert type { toBitVec := enumToBitVec, toBitVecLemma := lemma }
        toBitVecFns := toBitVecFns.insert enumToBitVec

      let interestingMatchers := analysis.interestingMatchers
      for (matcher, kind) in interestingMatchers do
        let lemma ← getMatchEqCondForAux matcher kind
        relevantLemmas := relevantLemmas.insert (← Sym.Simp.mkTheoremFromDecl lemma)

      methods := { methods with
        pre := methods.pre
          >> applyIteSimproc toBitVecFns
          >> applyCondSimproc toBitVecFns
        post := methods.post
          >> relevantLemmas.rewrite
          >> enumEqToBitVecEq enumIndex
          >> enumToBitVecCtor
      }

      -- Desugaring matches could have potentially revealed new opportunities to do stuff with
      -- structures. Thus we must also re run lemmas that handle structure projections in the
      -- presence of control flow.
      let cfg ← PreProcessM.getConfig
      methods ← addDefaultTypeAnalysisLemmas methods
      if cfg.structures then
        methods ← addStructureSimpLemmas methods

      -- same for fixed integers
      if cfg.fixedInt then
        methods ← addIntToBitVecLemmas goal methods

      let cfg ← PreProcessM.getConfig
      let config := {
        maxSteps := cfg.maxSteps
      }

      let solved ← PreProcessM.mapSimpHyps methods config
      if solved then return true
      discard <| postprocess goal |>.run' {}
      return false
where
  postprocess (goal : MVarId) : StateRefT PostProcessState PreProcessM Unit :=
    goal.withContext do
      let filter e :=
        if let .app (.const (.str _ s) ..) _ := e then
          s == enumToBitVecSuffix && !e.hasLooseBVars
        else
          false

      let analysis ← PreProcessM.getTypeAnalysis
      let mut relevantIndex : Std.HashSet Name := {}
      for enum in analysis.interestingEnums do
        let domainSize := (← getConstInfoInduct enum).ctors.length
        if domainSize.isPowerOfTwo then continue
        relevantIndex := relevantIndex.insert enum

      let processor e := do
        /-
        It is important that we maintain our own cache here in addition to the one of
        `forEachWhere`. This is because we call `forEachWhere` on multiple hypotheses and two
        hypotheses could contain the same term but we still do not want to duplicate bounds
        hypotheses for it.
        -/
        if (← get).seen.contains ⟨e⟩ then return ()
        let .app (.const (.str enumType _) ..) val := e | unreachable!
        unless relevantIndex.contains enumType do return ()
        let value ← Sym.share <| ← mkAppM (← getEnumToBitVecLeFor enumType) #[val]
        let type ← Sym.inferType value
        let hyp := { name := .anonymous, type, value, source := .enumDomain enumType }
        PreProcessM.pushHyp hyp
        modify fun s => { s with seen := s.seen.insert ⟨e⟩ }

      PreProcessM.forHyps fun hyp =>
        hyp.type.forEachWhere (stopWhenVisited := true) filter processor

end Normalize
end Lean.Meta.Tactic.BVDecide
