/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Elab.PreDefinition
import Lean.Elab.PreDefinition
import Lean.Meta.Constructions.CtorElim
import Lean.Meta.Constructions.CtorIdx

public section

namespace Lean.Meta.CmpHelper

inductive Kind where
  | beq
  | ord
deriving Repr

def Kind.indicatorType : Kind → Expr
  | .beq => .const ``Bool []
  | .ord => .const ``Ordering []

def Kind.eqIndicator : Kind → Expr
  | .beq => .const ``true []
  | .ord => .const ``Ordering.eq []

def Kind.compareIndices : Kind → Nat → Nat → Expr
  | .beq, a, b => toExpr (a == b)
  | .ord, a, b => toExpr (compare a b)

def Kind.falseBranch : Kind → Expr → Expr → Expr
  | .beq, _, _ => .const ``false []
  | .ord, a, b => mkApp4 (.const ``compare [0]) Nat.mkType (.const ``instOrdNat []) a b

def Kind.chain : Kind → Expr
  | .beq => .const ``and []
  | .ord => .const ``Ordering.then []

def Kind.dependentChain : Kind → Expr
  | .beq => .const ``Bool.dand []
  | .ord => .const ``Ordering.dthen []

def Kind.chainIntro : Kind → Expr
  | .beq => .const ``Bool.and_eq_true_of_eq_true []
  | .ord => .const ``Ordering.then_eq_eq_of_eq_eq []

def Kind.chainLeft : Kind → Expr
  | .beq => .const ``Bool.left_eq_true_of_and_eq_true []
  | .ord => .const ``Ordering.left_eq_eq_of_then_eq_eq []

def Kind.chainRight : Kind → Expr
  | .beq => .const ``Bool.right_eq_true_of_and_eq_true []
  | .ord => .const ``Ordering.right_eq_eq_of_then_eq_eq []

def Kind.dependentChainIntro : Kind → Expr
  | .beq => .const ``Bool.dand_eq_true_of_eq_true []
  | .ord => .const ``Ordering.dthen_eq_eq_of_eq_eq []

def Kind.dependentChainLeft : Kind → Expr
  | .beq => .const ``Bool.left_eq_true_of_dand_eq_true []
  | .ord => .const ``Ordering.left_eq_eq_of_dthen_eq_eq []

def Kind.dependentChainRight : Kind → Expr
  | .beq => .const ``Bool.right_eq_true_of_dand_eq_true []
  | .ord => .const ``Ordering.right_eq_eq_of_dthen_eq_eq []

def Kind.mkHelperName : Kind → Name → Name
  | .beq, nm => .str nm "_beqHelper"
  | .ord, nm => .str nm "_ordHelper"

def Kind.mkEq (k : Kind) (e : Expr) : Expr :=
  mkApp3 (.const ``Eq [1]) k.indicatorType e k.eqIndicator

def Kind.mkCtorIdxLemmaName (k : Kind) (indName : Name) : Name :=
  (k.mkHelperName indName).str "of_ctorIdx_ne"

def Kind.mkUnfoldName (k : Kind) (indName ctorName : Name) : Name :=
  (k.mkHelperName indName).str "unfold" |>.appendCore <| ctorName.replacePrefix indName .anonymous

def Kind.mkReflName (k : Kind) (indName : Name) : Name :=
  (k.mkHelperName indName).str "refl"

/--
Given all variables for a minor, returns `(fields, idxOfField, ihs)`.
-/
def decodeMinorVars (vars : Array Expr) (idxOfMotive : FVarIdMap Nat) :
    MetaM (Array Expr × FVarIdMap Nat × Array (Option Expr)) := do
  let mut fields := #[]
  let mut idxOfField := {}
  let mut ihs := #[]
  for var in vars do
    let ty ← inferType var
    if let .fvar f := ty.getForallBody.getAppFn then
      if idxOfMotive.contains f then
        let thing := ty.getForallBody.appArg!.getAppFn.fvarId!
        ihs := ihs.set! (idxOfField.get! thing) (some var)
        continue
    idxOfField := idxOfField.insert var.fvarId! fields.size
    fields := fields.push var
    ihs := ihs.push none
  return (fields, idxOfField, ihs)

def _root_.Lean.Meta.DiscrTree.Trie.atKey (x : DiscrTree.Trie α)
    (keys : Array DiscrTree.Key) (i : Nat) : Array α :=
  let .node vs children := x
  if h : i < keys.size then
    if let some entry := children.binSearch (keys[i], default) (fun a b => a.1 < b.1) then
      entry.2.atKey keys (i + 1)
    else
      #[]
  else
    vs
termination_by keys.size - i

def _root_.Lean.Meta.DiscrTree.atKey (x : DiscrTree α) (keys : Array DiscrTree.Key) :
    Array α :=
  if h : keys.size = 0 then
    #[]
  else
    (x.root.find? keys[0]).map (·.atKey keys 1) |>.getD #[]

inductive CmpHelperStrategy where
  | doubleMatch
  | withCtorIdx

def makePreDefinitionWithStructuralHint (levelParams : List Name) (declName : Name)
    (type value : Expr) (majorIdx : Nat) (numArgs : Nat) (isUnsafe : Bool) (makePartial : Bool) :
    MetaM Elab.PreDefinition := do
  let ref ← getRef
  return {
    ref, levelParams, type, value, declName
    kind := .def
    modifiers := {
      recKind := if makePartial && !isUnsafe then .partial else .default
      attrs := #[{
        name := `specialize
        stx := Unhygienic.run `(attr| specialize)
      }]
      isUnsafe
    }
    binders := .missing
    termination := if makePartial || isUnsafe then .none else {
      ref
      terminationBy?? := none
      terminationBy? := some {
        ref
        structural := true
        vars := #[mkIdent `x]
        body := mkIdent `x
      }
      partialFixpoint? := none
      decreasingBy? := none
      extraParams := numArgs - majorIdx
      noWarnOnRedundant := true
    }
  }

def makeCmpHelperDoubleMatch (kind : Kind) (levelParams : List Name) (lparams : List Level)
    (params : Array Expr) (moreVars : Array Expr) (indName : Name) (ctorCases : Array Expr)
    (makePartial : Bool) : MetaM Elab.PreDefinition := do
  let info ← getConstInfoInduct indName
  let casesOnAppBase := mkAppN (.const (mkCasesOnName indName) (1 :: lparams)) params
  let casesOnType ← inferType casesOnAppBase
  let .forallE _ motiveType body _ := casesOnType | unreachable!
  forallTelescope motiveType fun lvars _ => do
  forallTelescope motiveType fun rvars _ => do
  let motive ← mkLambdaFVars lvars kind.indicatorType
  let casesOnAppBase := casesOnAppBase.app motive
  let outerCasesOn := mkAppN casesOnAppBase lvars
  let innerCasesOnBase := mkAppN casesOnAppBase rvars
  let altsType := (body.instantiate1 motive).getForallBodyMaxDepth lvars.size
  let mut outerIter := altsType
  let mut i := 0
  let mut outerApp := outerCasesOn
  repeat
    let .forallE _ laltType more _ := outerIter | break
    outerApp := outerApp.app <| ← forallTelescope laltType fun lfields _ => do
      let mut innerIter := altsType
      let mut j := 0
      let mut innerApp := innerCasesOnBase
      repeat
        let .forallE _ raltType more _ := innerIter | break
        innerApp := innerApp.app <| ← forallTelescope raltType fun rfields _ => do
          let val ←
            if i = j then
              instantiateMVars <| ctorCases[i]!.beta (lfields ++ rfields)
            else
              pure <| kind.compareIndices i j
          mkLambdaFVars rfields val
        innerIter := more
        j := j + 1
      mkLambdaFVars lfields innerApp
    outerIter := more
    i := i + 1
  let type ← mkForallFVars (params ++ moreVars ++ lvars ++ rvars) kind.indicatorType (binderInfoForMVars := .default)
  let value ← mkLambdaFVars (params ++ moreVars ++ lvars ++ rvars) outerApp (binderInfoForMVars := .default)
  makePreDefinitionWithStructuralHint levelParams (kind.mkHelperName indName) type value
    (params.size + moreVars.size + lvars.size - 1)
    (params.size + moreVars.size + lvars.size + rvars.size)
    info.isUnsafe makePartial

def makeCmpHelperCtorIdx (kind : Kind) (levelParams : List Name) (lparams : List Level)
    (params : Array Expr) (moreVars : Array Expr) (indName : Name) (ctorCases : Array Expr)
    (makePartial : Bool) : MetaM Elab.PreDefinition := do
  let info ← getConstInfoInduct indName
  let casesOnApp := mkAppN (.const (mkCasesOnName indName) (1 :: lparams)) params
  let casesOnType ← inferType casesOnApp
  let .forallE _ motiveType body _ := casesOnType | unreachable!
  forallTelescope motiveType fun lvars _ => do
  forallTelescope motiveType fun rvars _ => do
  let lctorIdx := mkAppN (mkAppN (.const (mkCtorIdxName indName) lparams) params) lvars
  let rctorIdx := mkAppN (mkAppN (.const (mkCtorIdxName indName) lparams) params) rvars
  let ctorIdxEq := mkApp3 (.const ``Eq [1]) Nat.mkType rctorIdx lctorIdx
  let ctorIdxEqImp := .forallE `hcidx ctorIdxEq kind.indicatorType .default
  let motive ← mkLambdaFVars lvars ctorIdxEqImp
  let innerMotive ← mkLambdaFVars rvars kind.indicatorType
  let mut casesOnApp := mkAppN (casesOnApp.app motive) lvars
  let mut altsType := (body.instantiate1 motive).getForallBodyMaxDepth lvars.size
  let mut i := 0
  let mut ctors := info.ctors
  repeat
    let ctor :: moreCtors := ctors | break
    let .forallE _ laltType more _ := altsType | break
    casesOnApp := casesOnApp.app <| ← forallTelescope laltType fun lfields _ => do
      withLocalDeclD `hidx (mkApp3 (.const ``Eq [1]) Nat.mkType rctorIdx (.lit (.natVal i))) fun hidx => do
      let innerApp := mkAppN (.const (mkConstructorElimName indName ctor) (1 :: lparams)) params
      let innerApp := (mkAppN (innerApp.app innerMotive) rvars).app hidx
      let minor ← forallTelescope laltType fun rfields _ => do
        mkLambdaFVars rfields <| ← instantiateMVars <| ctorCases[i]!.beta (lfields ++ rfields)
      let mut innerApp := innerApp.app minor
      if lfields.isEmpty then
        innerApp := minor
      mkLambdaFVars (lfields.push hidx) innerApp
    ctors := moreCtors
    altsType := more
    i := i + 1
  let ctorIdxBEq := mkApp2 (.const ``Nat.beq []) rctorIdx lctorIdx
  let ctorIdxBEqEq := mkApp2 (.const ``Eq [1]) (.const ``Bool []) ctorIdxBEq
  let ctorIdxBEqEqRefl := mkApp2 (.const ``rfl [1]) (.const ``Bool []) ctorIdxBEq
  let ctorIdxEqImp := .forallE `hidx (.app ctorIdxBEqEq (.bvar 0)) kind.indicatorType .default
  let motive := .lam `b (.const ``Bool []) ctorIdxEqImp .default
  let falseBranch := .lam `hidx (.app ctorIdxBEqEq (.const ``false [])) (kind.falseBranch lctorIdx rctorIdx) .default
  let trueBranch :=
    .lam `hidx (.app ctorIdxBEqEq (.const ``true []))
      (.app casesOnApp (mkApp3 (.const ``Nat.eq_of_beq_eq_true []) rctorIdx lctorIdx (.bvar 0)))
      .default
  let boolCases := mkApp5 (.const ``Bool.casesOn [1]) motive ctorIdxBEq falseBranch trueBranch ctorIdxBEqEqRefl
  let type ← mkForallFVars (params ++ moreVars ++ lvars ++ rvars) kind.indicatorType (binderInfoForMVars := .default)
  let value ← mkLambdaFVars (params ++ moreVars ++ lvars ++ rvars) boolCases (binderInfoForMVars := .default)
  makePreDefinitionWithStructuralHint levelParams (kind.mkHelperName indName) type value
    (params.size + moreVars.size + lvars.size - 1)
    (params.size + moreVars.size + lvars.size + rvars.size)
    info.isUnsafe makePartial

def makeCmpHelperEquation (kind : Kind) (levelParams : List Name) (lparams : List Level)
    (params : Array Expr) (moreVars : Array Expr) (indName ctorName : Name) (eqn : Expr) :
    MetaM Unit := do
  let unfoldThm? ← getUnfoldEqnFor? (kind.mkHelperName indName)
  lambdaTelescope eqn fun allFields res => do
    let lfields := allFields[0...allFields.size/2]
    let rfields := allFields[(allFields.size/2)...*]
    let lctorApp := mkAppN (mkAppN (.const ctorName lparams) params) lfields
    let rctorApp := mkAppN (mkAppN (.const ctorName lparams) params) rfields
    let ltype ← inferType lctorApp
    let rtype ← inferType rctorApp
    assert! ltype.getAppFn.isConstOf indName
    assert! rtype.getAppFn.isConstOf indName
    let lindices := ltype.getAppArgs.drop params.size
    let rindices := rtype.getAppArgs.drop params.size
    let helperApp := mkAppN (mkAppN (.const (kind.mkHelperName indName) lparams) params) moreVars
    let helperApp := (mkAppN ((mkAppN helperApp lindices).app lctorApp) rindices).app rctorApp
    let eq := mkApp3 (.const ``Eq [1]) kind.indicatorType helperApp res
    let mut proof := mkApp2 (.const ``rfl [1]) kind.indicatorType helperApp
    if let some thm := unfoldThm? then
      proof := mkAppN (mkAppN (.const thm lparams) params) moreVars
      proof := (mkAppN ((mkAppN proof lindices).app lctorApp) rindices).app rctorApp
    let type ← mkForallFVars (params ++ moreVars ++ allFields) eq (binderInfoForMVars := .default)
    let value ← mkLambdaFVars (params ++ moreVars ++ allFields) proof (binderInfoForMVars := .default)
    addDecl <| .thmDecl {
      name := kind.mkUnfoldName indName ctorName
      levelParams, type, value
    }

def makeCmpHelpersFromEquations (kind : Kind) (levelParams : List Name) (lparams : List Level)
    (params : Array Expr) (moreVars : Array Expr) (cases : Array (Name × Array Expr))
    (makePartial : Bool) : MetaM Unit := do
  let mut predefs : Array Elab.PreDefinition := #[]
  for (indName, ctorCases) in cases do
    if ctorCases.size ≤ 5 then
      let predef ← makeCmpHelperDoubleMatch kind levelParams lparams params moreVars indName ctorCases makePartial
      predefs := predefs.push predef
    else
      let predef ← makeCmpHelperCtorIdx kind levelParams lparams params moreVars indName ctorCases makePartial
      predefs := predefs.push predef
  withLCtx {} {} do
    withExporting (isExporting := cases.all (!isPrivateName ·.1)) do
      Elab.Term.TermElabM.run' <| Elab.addPreDefinitions ({}, {}) predefs
  if makePartial then return
  for (indName, cases) in cases do
    let info ← getConstInfoInduct indName
    let ctors := info.ctors
    for ctor in ctors, eqn in cases do
      makeCmpHelperEquation kind levelParams lparams params moreVars indName ctor eqn

partial def computeFwdAndBackDeps (vars : Array Expr) (idxOfVar : FVarIdMap Nat) :
    MetaM (Array (Array Nat) × Array (Array Nat)) := do
  -- j ∈ backDeps[i] ↔ fields[i] depends on fields[j]
  -- j ∈ fwdDeps[i] ↔ fields[j] depends on fields[i]
  let mut backDeps : Array (Array Nat) := Array.emptyWithCapacity vars.size
  let mut fwdDeps : Array (Array Nat) := Array.replicate vars.size #[]
  for h : j in 0...vars.size do
    let field := vars[j]
    let type ← inferType field
    let state := collectFVars {} type
    let mut myBackDeps := #[]
    for var in state.fvarIds do
      let some i := idxOfVar.get? var | continue
      if myBackDeps.contains i then
        continue
      myBackDeps := myBackDeps.push i
      for i' in backDeps[i]! do
        if myBackDeps.contains i' then
          continue
        myBackDeps := myBackDeps.push i'
    for dep in myBackDeps do
      fwdDeps := fwdDeps.modify dep (·.push j)
    backDeps := backDeps.push myBackDeps.qsort
  return (fwdDeps, backDeps)

structure FnAccumulatorEntry where
  idx : Nat
  typeLambda : Expr
  fnMVar : Expr
  hypMVar? : Option Expr
deriving Inhabited

def FnAccumulatorEntry.addHyp (kind : Kind) (e : FnAccumulatorEntry) : MetaM FnAccumulatorEntry := do
  if e.hypMVar?.isSome then
    return e
  let fnType ← inferType e.fnMVar
  let hypType ← forallTelescope fnType fun vars _ => do
    let a := vars[vars.size - 2]!
    let b := vars[vars.size - 1]!
    let eqType := kind.mkEq <| mkAppN e.fnMVar vars
    mkForallFVars vars <| .forallE `heq eqType (← mkEq a b) .default
  let hypMVar ← mkFreshExprSyntheticOpaqueMVar hypType (`h |>.appendIndexAfter (e.idx + 1))
  return { e with hypMVar? := hypMVar }

structure FnAccumulator where
  paramLCtx : LocalContext
  paramInsts : LocalInstances
  entries : Array FnAccumulatorEntry := #[]
  tree : DiscrTree Nat := .empty
deriving Inhabited

def FnAccumulator.insert (acc : FnAccumulator) (kind : Kind) (typeLambda : Expr) (dep : Bool) :
    MetaM (FnAccumulatorEntry × FnAccumulator) := do
  if typeLambda.hasAnyFVar (!acc.paramLCtx.contains ·) then
    throwError "Invalid accumulated entry{indentExpr typeLambda}\nnot every dependency was eliminated"
  withLCtx acc.paramLCtx acc.paramInsts do
    let (_, _, e) ← lambdaMetaTelescope typeLambda
    let path ← DiscrTree.mkPath e
    let keyedEntries := acc.tree.atKey path
    for h : j in *...keyedEntries.size do
      let entryIdx := keyedEntries[j]
      let entry := acc.entries[entryIdx]!
      if ← isDefEqI entry.typeLambda typeLambda then
        if dep && entry.hypMVar?.isNone then
          let entries ← acc.entries.modifyM entryIdx (·.addHyp kind)
          return (entries[entryIdx]!, { acc with entries })
        else
          return (entry, acc)
    let fnType ← lambdaTelescope typeLambda fun vars body => do
      withLocalDeclD `a body fun avar => do
      withLocalDeclD `b body fun bvar => do
        mkForallFVars (vars.push avar |>.push bvar) kind.indicatorType
    let idx := acc.entries.size
    let fnMVar ← mkFreshExprSyntheticOpaqueMVar fnType (`f |>.appendIndexAfter (idx + 1))
    let mut newEntry : FnAccumulatorEntry := { idx, typeLambda, fnMVar, hypMVar? := none }
    if dep then
      newEntry ← newEntry.addHyp kind
    let entries := acc.entries.push newEntry
    let tree := acc.tree.insertKeyValue path idx
    return (newEntry, { acc with entries, tree })

def recursorAltToEquation (kind : Kind) (alt : Expr) (idxOfMotive : FVarIdMap Nat)
    (cmpFnsByMotiveIdx : Array Expr) : StateT FnAccumulator MetaM Expr := do
  forallTelescope alt fun lhsVars _ => do
    let (lhsFields, idxOfLhsField, lhsIHs) ← decodeMinorVars lhsVars idxOfMotive
    -- j ∈ allFwdDeps[i] ↔ fields[j] depends on fields[i]
    -- j ∈ allBackDeps[i] ↔ fields[i] depends on fields[j]
    let (allFwdDeps, allBackDeps) ← computeFwdAndBackDeps lhsFields idxOfLhsField
    let rec makeCmp (i : Nat) (rhsFields : Array Expr) : StateT FnAccumulator MetaM Expr := do
      if h : i < lhsFields.size then
        let lhsField := lhsFields[i]
        let rhsField := rhsFields[i]!
        let fwdDeps := allFwdDeps[i]!
        let fieldType ← inferType lhsField
        if let some ih := lhsIHs[i]! then
          unless fwdDeps.isEmpty do
            throwError "Unexpected forward dependencies at recursive occurrence {lhsField}"
          let .app leftMotiveApp _field ← inferType ih | unreachable!
          let motiveIdx := idxOfMotive.get! leftMotiveApp.getAppFn.fvarId!
          let indices := leftMotiveApp.getAppArgs
          let cmpFn := cmpFnsByMotiveIdx[motiveIdx]!
          let cmp := (mkAppN ((mkAppN cmpFn indices).app lhsField) indices).app rhsField
          if i + 1 = lhsFields.size then
            return cmp
          let more ← makeCmp (i + 1) rhsFields
          return mkApp2 kind.chain cmp more
        else if ← Meta.isProp fieldType then
          makeCmp (i + 1) rhsFields
        else
          let fwdDeps := allFwdDeps[i]!
          let backDeps := allBackDeps[i]!
          let backDepVars := backDeps.map (lhsFields[·]!)
          let isDep := !fwdDeps.isEmpty
          let entry ← StateT.mk fun acc => do
            acc.insert kind (← mkLambdaFVars backDepVars fieldType) isDep
          let cmp := mkApp2 (mkAppN entry.fnMVar backDepVars) lhsField rhsField
          if isDep then
            withLocalDeclD `heq (kind.mkEq cmp) fun heqVar => do
              -- hyp : lhsField = rhsField
              let hyp := mkApp3 (mkAppN entry.hypMVar?.get! backDepVars) lhsField rhsField heqVar
              -- Construct an Eq.ndrec term
              let fwdDepVars := fwdDeps.map (rhsFields[·]!)
              let motive ← mkForallFVars fwdDepVars kind.indicatorType
              let motiveSort ← getLevel motive
              let motive ← mkLambdaFVars #[rhsField] motive
              forallTelescope (motive.beta #[lhsField]) fun newFwdDepVars _ => do
                let mut rhsFields := rhsFields
                for dep in fwdDeps, newVar in newFwdDepVars do
                  rhsFields := rhsFields.set! dep newVar
                let more ← makeCmp (i + 1) rhsFields
                let refl ← mkLambdaFVars newFwdDepVars more
                let ndrecApp := mkApp6 (.const ``Eq.ndrec [motiveSort, ← getLevel fieldType])
                  fieldType lhsField motive refl rhsField hyp
                let ndrecApp := mkAppN ndrecApp fwdDepVars
                return mkApp2 kind.dependentChain cmp <| ← mkLambdaFVars #[heqVar] ndrecApp
          else if i + 1 = lhsFields.size then
            return cmp
          else
            let more ← makeCmp (i + 1) rhsFields
            return mkApp2 kind.chain cmp more
      else
        return kind.eqIndicator
    forallBoundedTelescope alt lhsFields.size fun rhsFields _ => do
      mkLambdaFVars (lhsFields ++ rhsFields) (← makeCmp 0 rhsFields)

/--
Note: for nested inductives, we currently use `partial`, making it impossible to derive any
meaningful laws.
-/
partial def makeCmpHelpers (indName : Name) (kind : Kind) : MetaM Unit := do
  let info ← getConstInfoInduct indName
  let usePartial := info.isNested
  let recInfo ← getConstInfoRec (mkRecName indName)
  let levelParams := info.levelParams
  let lparams := levelParams.map Level.param
  forallBoundedTelescope recInfo.type recInfo.numParams fun params body => do
    let acc : FnAccumulator := {
      paramLCtx := ← getLCtx
      paramInsts := ← getLocalInstances
    }
    forallTelescope body fun vars _ => do
      let motives := vars[0...recInfo.numMotives]
      let mut idxOfMotive := {}
      let mut cmpVars := #[]
      for i in *...recInfo.numMotives do
        idxOfMotive := idxOfMotive.insert motives[i]!.fvarId! i
        let motiveType ← inferType motives[i]!
        let cmpVarType ← forallTelescope motiveType fun vars _ => do
          mkForallFVars vars (← mkForallFVars vars kind.indicatorType)
        let cmpVar ← mkFreshExprSyntheticOpaqueMVar cmpVarType <| (`cmp).appendIndexAfter (i + 1)
        cmpVars := cmpVars.push cmpVar
      let alts := vars[recInfo.numMotives...(recInfo.numMotives + recInfo.numMinors)]
      let mut acc := acc
      let mut eqns : Array (Name × Array Expr) := info.all.toArray.map (·, #[])
      for alt in alts do
        let ty ← inferType alt
        let motiveIdx := idxOfMotive.get! ty.getForallBody.getAppFn.fvarId!
        unless motiveIdx < eqns.size do continue
        let (eqn, newAcc) ← (recursorAltToEquation kind ty idxOfMotive cmpVars).run acc
        eqns := eqns.modify motiveIdx fun (nm, xs) => (nm, xs.push eqn)
        acc := newAcc
      let moreVars := acc.entries.map (·.fnMVar) ++ acc.entries.filterMap (·.hypMVar?)
      for i in *...eqns.size do
        let cmpMVar := cmpVars[i]!.mvarId!
        let indName := eqns[i]!.1
        cmpMVar.assign (mkAppN (mkAppN (.const (kind.mkHelperName indName) lparams) params) moreVars)
      for i in *...info.numNested do
        let _cmpMVar := cmpVars[i + eqns.size]!.mvarId!
        throwError "TODO: Implement nested cmpVar assignment"
      makeCmpHelpersFromEquations kind levelParams lparams params moreVars eqns (usePartial || info.isUnsafe)

structure CtorInfo where
  /--
  A lambda of type `constructor fields of a → constructor fields of b → indicatorType` where the
  body has a certain shape.
  -/
  unfoldResult : Expr
  /--
  A proof that `∀ c..., ∀ d..., cmpVars[motiveIdx] ⋯ (ctor c...) ⋯ (ctor d...) = unfoldResult ctorFieldsA... ctorFieldsB...`
  -/
  unfoldLemma : Expr
deriving Inhabited

instance : ToMessageData CtorInfo where
  toMessageData x := .group <| .nestD <| m!"\{ unfoldResult := {x.unfoldResult},{Format.line}unfoldLemma := {x.unfoldLemma} }"

inductive VarClassification where
  | function (i : Nat)
  | cmpVar (i : Nat)
deriving Inhabited, Repr

instance : ToMessageData VarClassification where
  toMessageData x := repr x

structure Context where
  /-- The kind of comparison function we're deriving -/
  kind : Kind
  /-- All parameters for the helper functions -/
  allParams : Array Expr
  /-- The parameters of the recursor -/
  params : Array Expr
  /-- The auxiliary functions -/
  functions : Array Expr
  /-- The `∀ vars..., functions[i] vars... a b = eqIndicator → a = b` hypotheses if needed -/
  hyps : Array (Option Expr)
  /--
  For each motive, a let declaration of type:
  indices of `a` → `a` → indices of `b` → `b` → indicatorType
  -/
  cmpVars : Array Expr
  /--
  Names for the helper we want to export lemmas for (in motive order).
  -/
  associatedNames : Array (Option Name)
  /--
  For each motive, a proof of `cmpVars[i] ⋯ a ⋯ b = eqIndicator → a.ctorIdx = b.ctorIdx`
  -/
  ctorIdxLemmas : Array Expr
  /--
  For each minor in order, some information.
  -/
  ctorInfos : Array CtorInfo
  /--
  `varInfo[var]? = .inl i ↔ functions[i]? = some var`
  `varInfo[var]? = .inr i ↔ cmpVars[i]? = some var`
  -/
  varInfo : FVarIdMap VarClassification
  /--
  Information for an arbitrary recursor.
  -/
  recInfo : RecursorVal

partial def makeRefl (ctx : Context) : MetaM Unit := do
  let recInfo := ctx.recInfo
  let elimLvlParam :: levelParams := recInfo.levelParams |
    throwError "Invalid level parameters for recursor"
  let type := recInfo.type.instantiateLevelParams [elimLvlParam] [.zero]
  let reflHypInfos ← ctx.functions.mapIdxM fun i fn => do
    forallTelescope (← inferType fn) fun fnVars _ => do
      let fnVars := fnVars.pop
      let last := fnVars.back!
      let type ← mkForallFVars fnVars (ctx.kind.mkEq (.app (mkAppN fn fnVars) last))
      return ((`refl).appendIndexAfter (i + 1), type)
  withLocalDeclsDND reflHypInfos fun reflHyps => do
  let type ← instantiateForall type ctx.params
  forallTelescope type fun recVars _ => do
    let motiveVars := recVars.take recInfo.numMotives
    let mut motives : Array Expr := .emptyWithCapacity recInfo.numMotives
    let mut idxOfMotive : FVarIdMap Nat := {}
    for i in 0...recInfo.numMotives do
      let some cmpVar := ctx.cmpVars[i]? |
        throwError "Comparison variable unavailable for motive at index {i}"
      let motiveVar := recVars[i]!
      let motive ← forallTelescope (← inferType motiveVar) fun vars _ => do
        let cmpApp := mkAppN (mkAppN cmpVar vars) vars
        mkLambdaFVars vars (ctx.kind.mkEq cmpApp)
      motives := motives.push motive
      idxOfMotive := idxOfMotive.insert motiveVar.fvarId! i
    let mut minors : Array Expr := .emptyWithCapacity recInfo.numMinors
    for i in 0...recInfo.numMinors do
      let minorVar := recVars[recInfo.numMotives + i]!
      let info := ctx.ctorInfos[i]!
      let minor ← forallTelescope (← inferType minorVar) fun vars body => do
        let (fields, idxOfField, ihs) ← decodeMinorVars vars idxOfMotive
        let motiveIdx := idxOfMotive.get! body.getAppFn.fvarId!
        let cmpFn := ctx.cmpVars[motiveIdx]!
        let motiveArgs := body.getAppArgs
        let comparison := mkAppN (mkAppN cmpFn motiveArgs) motiveArgs
        -- Prove `ctx.kind.mkEq e`
        let rec proveRefl (e : Expr) : MetaM Expr := do
          let fn := e.getAppFn
          if let .fvar f := fn then
            match ctx.varInfo.get! f with
            | .function i => return mkAppN reflHyps[i]! e.appFn!.getAppArgs
            | .cmpVar _i =>
              e.appArg!.withApp fun fn args => do
                let varIdx := idxOfField.get! fn.fvarId!
                let ih := ihs[varIdx]!.get!
                return mkAppN ih args
          else if fn == ctx.kind.eqIndicator then
            return mkApp2 (.const ``rfl [1]) ctx.kind.indicatorType fn
          else if fn == ctx.kind.chain then
            let #[lhs, rhs] := e.getAppArgs | unreachable!
            let leftProof ← proveRefl lhs
            let rightProof ← proveRefl rhs
            return mkApp4 ctx.kind.chainIntro lhs rhs leftProof rightProof
          else if fn == ctx.kind.dependentChain then
            let #[lhs, rhs] := e.getAppArgs | unreachable!
            let leftProof ← proveRefl lhs
            let rightProof ← proveRefl (rhs.betaRev #[leftProof])
            return mkApp4 ctx.kind.dependentChainIntro lhs rhs leftProof rightProof
          else if fn.isConstOf ``Eq.rec || fn.isConstOf ``Eq.ndrec then
            let args := e.getAppArgs
            -- the left and right hand sides should be syntactically equal (the same field)
            assert! args.size >= 6
            assert! args[1]! == args[4]!
            proveRefl (args[3]!.beta (args.drop 6))
          else
            throwError "Invalid goal for `CmpHelper.makeRefl.proveRefl`:{indentExpr e}"
        let unfoldLemma := mkAppN (mkAppN info.unfoldLemma fields) fields
        let unfolded := info.unfoldResult.beta (fields ++ fields)
        let proof ← proveRefl unfolded
        let proof := mkApp6 (.const ``Eq.trans [1]) ctx.kind.indicatorType
          comparison unfolded ctx.kind.eqIndicator unfoldLemma proof
        mkLambdaFVars vars proof
      minors := minors.push (minor.replaceFVars motiveVars motives)
    let recLParams := 0 :: recInfo.levelParams.tail.map Level.param
    let recArgs := ctx.params ++ motives ++ minors
    for motiveVar in motiveVars, name in ctx.associatedNames, cmpVar in ctx.cmpVars do
      let some name := name | continue
      let some cmpValue ← cmpVar.fvarId!.getValue? | throwError "{cmpVar} does not have a value"
      forallTelescope (← inferType motiveVar) fun motiveArgs _ => do
      let resType := ctx.kind.mkEq <| mkAppN (mkAppN cmpValue motiveArgs) motiveArgs
      let type ← mkForallFVars (ctx.allParams ++ reflHyps ++ motiveArgs) resType
      let recApp := mkAppN (.const (mkRecName name) recLParams) recArgs
      let value ← mkLambdaFVars (ctx.allParams ++ reflHyps) <| ← mkLetFVars ctx.cmpVars recApp
      addDecl <| .thmDecl {
        name := .str (ctx.kind.mkHelperName name) "refl"
        levelParams, type, value
      }

def withNonNestedContext (indName : Name) (kind : Kind) (k : Context → MetaM α) : MetaM α := do
  let indInfo ← getConstInfoInduct indName
  if indInfo.isNested then
    throwError "Invalid input to `withNonNestedContext`, expected non-nested inductive"
  let recInfo ← getConstInfoRec (mkRecName indName)
  let helper ← getConstVal <| kind.mkHelperName indName
  let associatedNames := indInfo.all.toArray.map some
  let nargs := helper.type.getForallArity
  let allParamsCount := nargs - 2 * (indInfo.numIndices + 1)
  forallBoundedTelescope helper.type (some allParamsCount) fun allParams _ => do
  let params := allParams.take indInfo.numParams
  let mut functions := #[]
  let mut hyps := #[]
  let mut varInfo := {}
  for h : i in indInfo.numParams...allParams.size do
    let var := allParams[i]'h.2
    let varType ← inferType var
    if varType.getForallBody == kind.indicatorType then
      varInfo := varInfo.insert var.fvarId! (.function functions.size)
      functions := functions.push var
      hyps := hyps.push none
    else
      let arity := varType.getForallArity
      let .forallE _ t _ _ := varType.getForallBodyMaxDepth (arity - 1) |
        throwError "Invalid hypothesis:{indentExpr varType}"
      let .fvar f := t.appFn!.appArg!.getAppFn |
        throwError "Invalid hypothesis:{indentExpr varType}"
      let some (.function i) := varInfo.get? f |
        throwError "Invalid hypothesis:{indentExpr varType}"
      hyps := hyps.set! i (some var)
  let lparams := helper.levelParams.map Level.param
  let rec addCmpVars (all : List Name) (cmpVars : Array Expr) (ctorIdxLemmas : Array Expr)
      (varInfo : FVarIdMap VarClassification) : MetaM α := do
    match all with
    | indName :: more =>
      let cmpVarName := (`cmp).appendIndexAfter (cmpVars.size + 1)
      let thing := mkAppN (.const (kind.mkHelperName indName) lparams) allParams
      let cidxLemma := mkAppN (.const (kind.mkCtorIdxLemmaName indName) lparams) allParams
      let index := cmpVars.size
      withLetDecl cmpVarName (← inferType thing) thing fun var => do
        addCmpVars more (cmpVars.push var) (ctorIdxLemmas.push cidxLemma)
          (varInfo.insert var.fvarId! (.cmpVar index))
    | [] =>
      let mut ctorInfos := #[]
      for indName in indInfo.all do
        for ctor in (← getConstInfoInduct indName).ctors do
          let lemmaName := kind.mkUnfoldName indName ctor
          let lemma := mkAppN (.const lemmaName lparams) allParams
          let res ← forallTelescope (← inferType lemma) fun bothCtorFields body => do
            let some (_, _, rhs) := body.eq? | throwError "Invalid lemma:{indentExpr lemma}"
            mkLambdaFVars bothCtorFields rhs
          let res := res.replace fun e => do
            let .const nm@(.str ind _) _ := e.getAppFn | none
            unless nm == kind.mkHelperName ind do none
            let args := e.getAppArgs
            if args.size < allParams.size then none
            return mkAppN cmpVars[indInfo.all.idxOf ind]! (args.drop allParams.size)
          ctorInfos := ctorInfos.push {
            unfoldResult := res
            unfoldLemma := lemma
          }
      let ctx := {
        kind, allParams, params, functions, hyps, cmpVars, associatedNames, ctorIdxLemmas,
        ctorInfos, varInfo, recInfo
      }
      k ctx
  addCmpVars indInfo.all #[] #[] varInfo
