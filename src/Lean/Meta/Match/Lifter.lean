/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Meta.Match.MatcherInfo
public import Lean.Meta.Match.MatchEqs
public import Lean.Meta.Tactic.FVarSubst
import Lean.Meta.Tactic.Subst

namespace Lean.Meta.Match

@[match_pattern, expose]
public def mkLifterName (matcherName : Name) : Name :=
  matcherName.str "lifter"

def proveLifterCore (matcherName : Name) (matcherInfo : MatcherInfo) (eqnInfo : MatchEqns) : MetaM Unit := do
  let val ← getConstVal matcherName
  let uElimPos := matcherInfo.uElimPos?.get!
  let lparams := val.levelParams.map Level.param
  let elimLvl := lparams[uElimPos]!
  let mut newUnivIdx := 1
  while val.levelParams.contains (`u |>.appendIndexAfter newUnivIdx) do
    newUnivIdx := newUnivIdx + 1
  let elimLevelParam' := (`u).appendIndexAfter newUnivIdx
  let elimLvl' := Level.param elimLevelParam'
  let lparams' := lparams.set uElimPos elimLvl'
  let numDiscrEqs := matcherInfo.getNumDiscrEqs
  let levelParams := elimLevelParam' :: val.levelParams
  let splitLParams := lparams.set uElimPos 0
  forallTelescope val.type fun vars _ => do
    let splitterName := eqnInfo.splitterName
    let splitterInfo := eqnInfo.splitterMatchInfo
    let params := vars[0...matcherInfo.numParams].toArray
    let motive := vars[matcherInfo.numParams]!
    let discrs := vars[matcherInfo.getFirstDiscrPos...matcherInfo.getFirstAltPos].toArray
    let alts := vars[matcherInfo.getFirstAltPos...matcherInfo.arity].toArray
    let motive'Type ← mkForallFVars discrs (.sort elimLvl')
    withLocalDeclD `motive' motive'Type fun motive' => do
    withLocalDeclD `f (← mkForallFVars discrs (← mkArrow (mkAppN motive discrs) (mkAppN motive' discrs))) fun fn => do
    let matchApp := mkAppN (.const matcherName lparams) vars
    let lhs := (mkAppN fn discrs).app matchApp
    let mut rhsAlts ← alts.mapM fun alt => do
      forallTelescope (← inferType alt) fun altVars altType => do
        assert! altType.getAppFn == motive
        mkLambdaFVars altVars ((mkAppN fn altType.getAppArgs).app (mkAppN alt altVars))
    let rhs := (mkAppN (.const matcherName lparams') params).app motive'
    let rhs := mkAppN (mkAppN rhs discrs) rhsAlts
    let eq := mkApp3 (.const ``Eq [elimLvl']) (mkAppN motive' discrs) lhs rhs
    let splitterMotive ← mkLambdaFVars discrs (← mkForallFVars alts eq)
    let splitterApp := (mkAppN (.const splitterName splitLParams) params).app splitterMotive
    let mut splitterApp := mkAppN splitterApp discrs
    let mut splitterType ← inferType splitterApp
    assert! alts.size ≤ splitterType.getForallArity
    for h : i in 0...splitterInfo.altInfos.size do
      let altInfo := splitterInfo.altInfos[i]
      let eqn? := eqnInfo.eqnNames[i]?
      let .forallE _ splitterAltType more _ := splitterType | unreachable!
      let altProof ← forallTelescopeReducing (whnfType := true) splitterAltType fun splitterVars eq => do
        let some (motive'App, lhs, rhs) := eq.eq? |
          throwError "Unexpected goal{indentExpr eq}\nin context{(← mkFreshExprMVar eq).mvarId!}"
        let some eqn := eqn? |
          mkLambdaFVars splitterVars (mkApp2 (.const ``rfl [elimLvl']) motive'App lhs)
        assert! motive'App.getAppFn == motive'
        assert! lhs.getAppFn == fn
        let motiveArgs := motive'App.getAppArgs
        let fstOverlapIdx := altInfo.numFields
        let fstEqnIdx := fstOverlapIdx + altInfo.numOverlaps
        let fstAltIdx := fstEqnIdx + numDiscrEqs + altInfo.hasUnitThunk.toNat
        let arity := fstAltIdx + alts.size
        let fields := splitterVars[0...fstOverlapIdx].toArray
        let overlaps := splitterVars[fstOverlapIdx...fstEqnIdx].toArray
        let eqns := splitterVars[fstEqnIdx...fstAltIdx].toArray
        let alts := splitterVars[fstAltIdx...arity].toArray
        let lproof := (mkAppN (.const eqn lparams) params).app motive
        let lproof := mkAppN (mkAppN (mkAppN lproof fields) alts) overlaps
        let some (_, _, mid) := (← inferType lproof).eq? | unreachable!
        let motiveApp := mkAppN motive motiveArgs
        let fnApp := lhs.appFn!
        let lhsMatch := lhs.appArg!
        -- f ... (match ... h_i ...) = f ... (h_i ...)
        let lproof := mkApp6 (.const ``congrArg [elimLvl, elimLvl'])
          motiveApp motive'App lhsMatch mid fnApp lproof
        -- The right-hand side is a match, the last arguments of which are the new alternatives
        let newAlts := rhs.getAppArgsN alts.size
        -- match ... (... => f ... (h_i ...)) ... = f ... (h_i ...)
        let rproof := (mkAppN (.const eqn lparams') params).app motive'
        let rproof := mkAppN (mkAppN (mkAppN rproof fields) newAlts) overlaps
        -- Finally, chain the proofs together
        let proof := mkApp6 (.const ``Eq.trans [elimLvl']) motive'App lhs (fnApp.app mid) rhs
          lproof (mkApp4 (.const ``Eq.symm [elimLvl']) motive'App rhs (fnApp.app mid) rproof)
        mkLambdaFVars splitterVars proof
      splitterApp := splitterApp.app altProof
      splitterType := more
    let varsInOrder := (params.push motive |>.push motive' |>.push fn) ++ discrs
    let value ← mkLambdaFVars varsInOrder splitterApp
    let type ← mkForallFVars (varsInOrder ++ alts) eq
    addDecl <| .thmDecl {
      name := mkLifterName matcherName
      levelParams, type, value
    }

def hasLifter (env : Environment) (name : Name) : Bool := Id.run do
  if let some info := getMatcherInfoCore? env name then
    return info.uElimPos?.isSome
  else
    let mkCasesOnName indName := name | return false
    let some info := isInductiveCore? env indName | return false
    let some val := env.findConstVal? name | return false
    if val.levelParams.length ≤ info.levelParams.length then
      return false
    return true

public def getPseudoMatcherInfo? (name : Name) : MetaM (Option MatcherInfo) := do
  if let some info ← getMatcherInfo? name then
    return some info
  let mkCasesOnName indName := name | return none
  let some info ← isInductive? indName | return none
  let val ← getConstVal name
  return some {
    numParams := info.numParams
    numDiscrs := info.numIndices + 1
    altInfos := ← info.ctors.toArray.mapM fun ctor => do
      let info ← getConstInfoCtor ctor
      pure {
        numFields := info.numFields
        numOverlaps := 0
        hasUnitThunk := false
      }
    uElimPos? := if val.levelParams.length ≤ info.levelParams.length then none else some 0
    discrInfos := Array.replicate (info.numIndices + 1) {}
    overlaps := {}
  }

def proveLifter (name : Name) : MetaM Bool := do
  if let some info ← getMatcherInfo? name then
    if info.uElimPos?.isSome then
      realizeConst name (mkLifterName name) <| withoutExporting do
        proveLifterCore name info (← getEquationsFor name)
      return true
    return false
  let mkCasesOnName indName := name | return false
  let some info ← isInductive? indName | return false
  let val ← getConstVal name
  if val.levelParams.length ≤ info.levelParams.length then
    return false
  let matcherInfo := {
    numParams := info.numParams
    numDiscrs := info.numIndices + 1
    altInfos := ← info.ctors.toArray.mapM fun ctor => do
      let info ← getConstInfoCtor ctor
      pure {
        numFields := info.numFields
        numOverlaps := 0
        hasUnitThunk := false
      }
    uElimPos? := some 0
    discrInfos := Array.replicate (info.numIndices + 1) {}
    overlaps := {}
  }
  realizeConst name (mkLifterName name) <| withoutExporting do
    proveLifterCore name matcherInfo {
      eqnNames := #[]
      splitterName := name -- `casesOn` also acts as the splitter
      splitterMatchInfo := matcherInfo
    }
  return true

public def getLifterFor? (name : Name) : MetaM (Option Name) := do
  if (← getEnv).contains (mkLifterName name) then
    return some (mkLifterName name)
  if ← proveLifter name then
    return some (mkLifterName name)
  return none

builtin_initialize
  registerReservedNamePredicate fun env nm =>
    match nm with
    | mkLifterName nm' => hasLifter env nm'
    | _ => false
  registerReservedNameAction fun nm => do
    match nm with
    | mkLifterName nm' => (proveLifter nm').run'
    | _ => pure false

end Lean.Meta.Match
