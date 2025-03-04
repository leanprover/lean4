/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Meta.Tactic.Simp
import Init.Data.Range.Basic

/-!
This module contains the implementation of the pre processing pass for handling equality on
enum inductive types.

The implementation generates mappings from enum inductives occuring in the goal to sufficiently
large `BitVec` and replaces equality on the enum inductives with equality on these mapping
functions.
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
Create a `cond` chain in `Type u` of the form:
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
        let inv ← mkCondChain 0 bvSize x declType ctors ctors.head!
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


-- TODO(henrik): Add further match statements like matches with default cases
/--
The various kinds of matches supported by the match to cond infrastructure.
-/
inductive MatchKind
  /--
  It is a full match statement on an enum inductive with one constructor handled per arm.
  -/
  | simpleEnum (info : InductiveVal)

/--
Determine whether `declName` is an enum inductive `.match_x` definition that is supported, see
`MatchKind` for the supported shapes.
-/
def matchIsSupported (declName : Name) : MetaM (Option MatchKind) := do
  let some info ← getMatcherInfo? declName | return none
  if info.discrInfos.size ≠ 1 then return none
  if info.discrInfos[0]!.hName?.isSome then return none
  let .defnInfo defnInfo ← getConstInfo declName | return none
  let kind : Option MatchKind ←
    forallTelescope defnInfo.type fun xs a => do
      if xs.size < 2 then return none
      -- Check that discriminator is `EnumInductive`
      let discr := xs[1]!
      let some discrTypeName := (← inferType discr).constName? | return none
      if !(← isEnumType discrTypeName) then return none
      let .inductInfo inductiveInfo ← getConstInfo discrTypeName | unreachable!

      -- Check that motive is `EnumInductive → Sort u`
      let motive := xs[0]!
      let motiveType ← inferType motive
      let some (.const domTypeName [], (.sort (.param ..))) := motiveType.arrow? | return none
      if domTypeName != discrTypeName then return none

      -- Check that remaining arguments are of form (Unit → motive EnumInductive.ctorN)
      let numCtors := inductiveInfo.numCtors
      if xs.size ≠ numCtors + 2 then return none
      for i in [0:numCtors] do
        let argType ← inferType <| xs[i + 2]!
        let some (.const ``Unit [], (.app m (.const c []))) := argType.arrow? | return none
        if m != motive then return none
        if inductiveInfo.ctors[i]! != c then return none

      -- Check that resulting type is `motive discr`
      a.withApp fun fn arg => do
        if fn != motive then return none
        if h : arg.size ≠ 1 then
          return none
        else
          if arg[0] != discr then return none
          return some <| .simpleEnum inductiveInfo

  match kind with
  | some (.simpleEnum inductiveInfo) =>
    lambdaTelescope defnInfo.value fun xs body =>
      body.withApp fun fn args => do
        -- Body is an application of `EnumInductive.casesOn`
        if !fn.isConstOf (mkCasesOnName inductiveInfo.name) then return none
        let numCtors := inductiveInfo.numCtors
        if args.size ≠ numCtors + 2 then return none
        -- first argument is `(fun x => motive x)`
        let firstArgOk ← lambdaTelescope args[0]! fun arg body => do
          if h : arg.size ≠ 1 then
            return false
          else
            let arg := arg[0]
            let .app fn arg' := body | return false
            return fn == xs[0]! && arg == arg'

        if !firstArgOk then return none

        -- second argument is discr
        if args[1]! != xs[1]! then return none

        -- remaining arguments are of the form `(h_n Unit.unit)`
        for i in [0:numCtors] do
          let .app fn (.const ``Unit.unit []) := args[i + 2]! | return none
          if fn != xs[i + 2]! then return none

        return some <| .simpleEnum inductiveInfo
  | none => return none

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
      withLocalDeclD `a (.sort (u.succ)) fun a => do
      withLocalDeclD `x (mkConst inductiveInfo.name) fun x => do
        let hType ← mkArrow (mkConst ``Unit) a
        let hBinders := inductiveInfo.ctors.foldl (init := #[]) (fun acc _ => acc.push (`h, hType))
        withLocalDeclsDND hBinders fun hs => do
          let args := #[mkLambda `x .default (mkConst inductiveInfo.name) a , x] ++ hs
          let lhs := mkAppN (mkConst declName [u.succ]) args
          let enumToBitVec := mkConst (← getEnumToBitVecFor inductiveInfo.name)
          let domainSize := inductiveInfo.ctors.length
          let bvSize := getBitVecSize domainSize
          let appliedHs := hs.toList.map (mkApp · (mkConst ``Unit.unit))
          let rhs ← mkCondChain u bvSize (mkApp enumToBitVec x) a appliedHs appliedHs[0]!
          let type := mkApp3 (mkConst ``Eq [u.succ]) a lhs rhs

          let motive ← mkLambdaFVars #[x] type
          let case h := do
            return mkApp (mkConst ``Eq.refl [u.succ]) <| (mkApp h (mkConst ``Unit.unit))
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
applications. If the specific `.match_x` that this is being called on is unsupported return `none`.
-/
def getMatchEqCondFor? (declName : Name) : MetaM (Option Name) := do
  if let some kind ← matchIsSupported declName then
    return some (← getMatchEqCondForAux declName kind)
  else
    return none

/--
Obtain a theorem that translates `.match_x` applications on enum inductives to chains of `cond`
applications. If the specific `.match_x` that this is being called on is unsupported throw an error.
-/
def getMatchEqCondFor (declName : Name) : MetaM Name := do
  if let some thm ← getMatchEqCondFor? declName then
    return thm
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

partial def enumsPass : Pass where
  name := `enums
  run' goal :=
    goal.withContext do
      let interesting := (← PreProcessM.getTypeAnalysis).interestingEnums
      if interesting.isEmpty then return goal
      let mut simprocs : Simprocs := {}
      let mut relevantLemmas : SimpTheoremsArray := #[]
      relevantLemmas ← relevantLemmas.addTheorem (.decl ``ne_eq) (← mkConstWithLevelParams ``ne_eq)
      for type in interesting do
        let lemma ← getEqIffEnumToBitVecEqFor type
        relevantLemmas ← relevantLemmas.addTheorem (.decl lemma) (mkConst lemma)

        let enumToBitVec ← getEnumToBitVecFor type
        let path : Array DiscrTree.Key := #[.const enumToBitVec 1, .star]
        simprocs := simprocs.addCore path ``enumToBitVecCtor true (.inl enumToBitVecCtor)

      let cfg ← PreProcessM.getConfig
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
  postprocess (goal : MVarId) : StateRefT (Array Hypothesis) MetaM MVarId :=
    goal.withContext do
      let filter e :=
        if let .app (.const (.str _ s) []) _ := e then
          s == enumToBitVecSuffix
        else
          false

      let processor e := do
        let .app (.const (.str enumType _) []) val := e | unreachable!
        let lemma := mkConst (← getEnumToBitVecLeFor enumType)
        let value := mkApp lemma val
        let type ← inferType value
        let hyp := { userName := .anonymous, type, value }
        modify fun s => s.push hyp

      for hyp in ← getPropHyps do
        (← hyp.getType).forEachWhere (stopWhenVisited := true) filter processor

      let hyps ← get
      if hyps.isEmpty then
        return goal
      else
        let (_, goal) ← goal.assertHypotheses hyps
        return goal

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
