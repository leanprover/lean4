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

/-!
# The match lifter theorem construction

For each matcher and `casesOn`, this module constructs the realizable constant `matcher.lifter`.
This theorem proves that applications on matchers can be moved into each alternative and is in this
sense similar to the theorems `apply_ite` and `apply_dite` available for if-then-else.

Unlike `apply_ite` and `apply_dite` however, the lifter theorems for matchers and `casesOn`s allow
for the function to depend on the discriminants.

The arguments to a lifter theorem are, in order:
1. The parameters for the matcher
2. The original motive
3. The new motive
4. The function applied to the matcher, mapping the original motive to the new motive
5. The discriminants for the matcher
6. The alternatives for the matcher

Furthermore, the lifter theorem has the same level parameters as the matcher with one additional in
front for the universe of the new motive. As an example, here is the lifter theorem for a simple
`List α` matcher:
```
theorem test.match_1.lifter.{u_3, u_1, u_2} : ∀ {α : Type u_1} (motive : List α → Sort u_2)
  {motive' : List α → Sort u_3} (f : (l : List α) → motive l → motive' l) (l : List α)
  (h_1 : Unit → motive []) (h_2 : (head : α) → (tail : List α) → motive (head :: tail)),
  f l
      (match l with
      | [] => h_1 ()
      | head :: tail => h_2 head tail) =
    match l with
    | [] => f [] (h_1 _)
    | head :: tail => f (head :: tail) (h_2 head tail) :=
```
-/

namespace Lean.Meta.Match

public def lifterSuffix := "lifter"

public def mkLifterName (matcherName : Name) : Name :=
  matcherName.str lifterSuffix

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
    withLocalDecl `motive' (← motive.fvarId!.getBinderInfo) motive'Type fun motive' => do
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
    for h : i in 0...splitterInfo.altInfos.size do
      let altInfo := splitterInfo.altInfos[i]
      let eqn? := eqnInfo.eqnNames[i]?
      let .forallE _ splitterAltType more _ := splitterType | unreachable!
      let altProof ← forallTelescopeReducing (whnfType := true) splitterAltType fun splitterVars eq => do
        let some (motive'App, lhs, rhs) := eq.eq? |
          throwError "Unexpected goal{indentExpr eq}\nin context{(← mkFreshExprMVar eq).mvarId!}"
        let some eqn := eqn? |
          -- this case is for `casesOn`s where we don't have equations
          -- instead, just prove this with `rfl`
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

/--
Only matchers and `casesOn`s that can eliminate into any universe have lifter theorems.
-/
def hasLifter (env : Environment) (name : Name) : Bool := Id.run do
  if let some info := getMatcherInfoCore? env name then
    return info.uElimPos?.isSome
  else
    let .str indName sfx := name | return false
    unless sfx == casesOnSuffix do return false
    let some info := isInductiveCore? env indName | return false
    let some val := env.findConstVal? name | return false
    if val.levelParams.length ≤ info.levelParams.length then
      return false
    return true

/--
Like `getMatcherInfo?` but also returns information for `casesOn` recursors.
-/
public def getPseudoMatcherInfo? (name : Name) : MetaM (Option MatcherInfo) := do
  if let some info ← getMatcherInfo? name then
    return some info
  let .str indName sfx := name | return none
  unless sfx == casesOnSuffix do return none
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
  let some info ← getPseudoMatcherInfo? name | return false
  if info.uElimPos?.isNone then return false
  realizeConst name (mkLifterName name) <| withoutExporting do
    let eqns ←
      if isCasesOnRecursor (← getEnv) name then
        pure {
          eqnNames := #[] -- just use `rfl` in the proof instead
          splitterName := name -- `casesOn` also acts as the splitter
          splitterMatchInfo := info
        }
      else getEquationsFor name
    proveLifterCore name info eqns
  return true

public def getLifterFor? (name : Name) : MetaM (Option Name) := do
  if (← getEnv).contains (mkLifterName name) then
    unless hasLifter (← getEnv) name do
      return none
    return some (mkLifterName name)
  if ← proveLifter name then
    return some (mkLifterName name)
  return none

builtin_initialize
  registerReservedNamePredicate fun env nm =>
    match nm with
    | .str nm' sfx => sfx == lifterSuffix && hasLifter env nm'
    | _ => false
  registerReservedNameAction fun nm => do
    match nm with
    | .str nm' sfx =>
      unless sfx == lifterSuffix do return false
      (proveLifter nm').run'
    | _ => pure false

end Lean.Meta.Match
