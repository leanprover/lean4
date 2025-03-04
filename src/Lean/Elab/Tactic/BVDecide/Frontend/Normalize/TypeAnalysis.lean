/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.SInt.Basic
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic

/-!
This file implements the type analysis pass for the structures and enum inductives pass. It figures
out which types and matches that occur either directly or transitively (e.g. through being
contained in a structure) qualify for further treatment by the structures or enum pass.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

/--
Determine whether `declName` is an enum inductive `.match_x` definition that is supported, see
`MatchKind` for the supported shapes.
-/
def isSupportedMatch (declName : Name) : MetaM (Option MatchKind) := do
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

partial def typeAnalysisPass : Pass where
  name := `typeAnalysis
  run' goal := do
    checkContext goal
    let analysis ← PreProcessM.getTypeAnalysis
    trace[Meta.Tactic.bv] m!"Type analysis found structures: {analysis.interestingStructures.toList}"
    trace[Meta.Tactic.bv] m!"Type analysis found enums: {analysis.interestingEnums.toList}"
    trace[Meta.Tactic.bv] m!"Type analysis found matchers: {analysis.interestingMatchers.keys}"
    return goal
where
  checkContext (goal : MVarId) : PreProcessM Unit := do
    goal.withContext do
      for decl in ← getLCtx do
        if !decl.isLet && !decl.isImplementationDetail then
          let type := decl.type
          if !(← typeCasesRelevant type) then
            lookForMatches type

  constInteresting (n : Name) : PreProcessM Bool := do
    let analysis ← PreProcessM.getTypeAnalysis
    if analysis.interestingStructures.contains n || analysis.interestingEnums.contains n then
      return true
    else if analysis.uninteresting.contains n then
      return false

    if isStructure (← getEnv) n then
      if ← interestingStructure n then
        PreProcessM.markInterestingStructure n
        return true
      else
        PreProcessM.markUninterestingConst n
        return false
    else if ← isEnumType n then
      PreProcessM.markInterestingEnum n
      return true
    else
      PreProcessM.markUninterestingConst n
      return false

  interestingStructure (n : Name) : PreProcessM Bool := do
    let constInfo ← getConstInfoInduct n
    if constInfo.isRec then
      return false

    let ctorTyp := (← getConstInfoCtor constInfo.ctors.head!).type
    let analyzer state arg := do return state || (← typeCasesRelevant (← arg.fvarId!.getType))
    let interesting ← forallTelescope ctorTyp fun args _ => args.foldlM (init := false) analyzer
    return interesting

  typeCasesRelevant (expr : Expr) : PreProcessM Bool := do
    match_expr expr with
    | BitVec n => return (← getNatValue? n).isSome
    | UInt8 => return true
    | UInt16 => return true
    | UInt32 => return true
    | UInt64 => return true
    | USize => return true
    | Int8 => return true
    | Int16 => return true
    | Int32 => return true
    | Int64 => return true
    | ISize => return true
    | Bool => return true
    | _ =>
      let some const := expr.getAppFn.constName? | return false
      constInteresting const

  lookForMatches (expr : Expr) : PreProcessM Unit := do
    expr.forEachWhere Expr.isConst fun e => do
      let .const declName .. := e | unreachable!
      if let some kind ← isSupportedMatch declName then
        PreProcessM.markInterestingMatcher declName kind

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
