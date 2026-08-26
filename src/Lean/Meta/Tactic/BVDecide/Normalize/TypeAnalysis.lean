/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Tactic.BVDecide.Attr
import Init.ByCases
import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.InstantiateMVarsS

/-!
This file implements the type analysis pass for the structures and enum inductives pass. It figures
out which types and matches that occur either directly or transitively (e.g. through being
contained in a structure) qualify for further treatment by the structures or enum pass.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

/--
Determine whether `declName` is an enum inductive `.match_x` definition that is supported, see
`MatchKind` for the supported shapes.
-/
public def isSupportedMatch (declName : Name) : MetaM (Option MatchKind) := do
  let some info ← getMatcherInfo? declName | return none
  if info.discrInfos.size ≠ 1 then return none
  if info.discrInfos[0]!.hName?.isSome then return none
  let .defnInfo defnInfo ← getConstInfo declName | return none
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
    let some (.const domTypeName .., (.sort (.param ..))) := motiveType.arrow? | return none
    if domTypeName != discrTypeName then return none

    -- Check that resulting type is `motive discr`
    let retTypeOk ← a.withApp fun fn arg =>
      return fn == motive && arg.size == 1 && arg[0]! == discr
    if !retTypeOk then return none
    let numCtors := inductiveInfo.numCtors

    /-
    At this point the control flow splits and tries to establish that the match is one of the kinds
    that we support.
    -/
    if xs.size == numCtors + 2 then
      /-
      This situation is most likely a full match but it could also be a match like:
      ```
      inductive Foo where
      | a
      | b

      def isA (f : Foo) : Bool :=
        match f with
        | .a => true
        | _ => false
      ```
      Where we have as many arms as constructors but the last arm is a default.
      -/

      if let some kind ← trySimpleEnum inductiveInfo xs numCtors motive then
        return kind

    if xs.size > 2 then
      -- Probably a match with default case

      -- Check that all parameters except the last are `h_n EnumInductive.ctor`
      let numConcreteCases := xs.size - 3 -- minus motive, discr and default case
      let mut handledCtors := Array.mkEmpty (xs.size - 3)
      for i in *...numConcreteCases do
        let argType ← inferType xs[i + 2]!
        let some (.const ``Unit [], (.app m (.const c ..))) := argType.arrow? | return none
        if m != motive then return none
        let .ctorInfo ctorInfo ← getConstInfo c | return none
        handledCtors := handledCtors.push ctorInfo

      -- Check that the last parameter looks like a default case one
      let defaultArgType ← inferType xs[xs.size - 1]!
      let defaultOk ← forallTelescope defaultArgType fun args dom => do
        if args.size != 1 then return false
        let input := args[0]!
        if !(← inferType input).isConstOf discrTypeName then return false
        return dom.withApp fun fn arg => fn == motive && arg.size == 1 && arg[0]! == input

      if !defaultOk then return none

      return some <| .enumWithDefault inductiveInfo handledCtors
    else
      return none
where
  trySimpleEnum (inductiveInfo : InductiveVal) (xs : Array Expr)
      (numCtors : Nat) (motive : Expr) : MetaM (Option MatchKind) := do
    -- Check that all parameters are `h_n EnumInductive.ctor`
    let mut handledCtors := Array.mkEmpty numCtors
    for i in *...numCtors do
      let argType ← inferType xs[i + 2]!
      let some (.const ``Unit [], (.app m (.const c ..))) := argType.arrow? | return none
      if m != motive then return none
      let .ctorInfo ctorInfo ← getConstInfo c | return none
      handledCtors := handledCtors.push ctorInfo

    return some <| .simpleEnum inductiveInfo handledCtors

def builtinTypes : Array Name :=
  #[``BitVec, ``Bool,
    ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize,
    ``Int8, ``Int16, ``Int32, ``Int64, ``ISize]

@[inline]
def isBuiltIn (n : Name) : Bool := builtinTypes.contains n

public def addDefaultTypeAnalysisLemmas (methods : Sym.Simp.Methods) :
    PreProcessM Sym.Simp.Methods := do
  let mut lemmas : Sym.Simp.Theorems := {}
  let relevantNames := #[
    ``dite_eq_ite,
    ``Std.Tactic.BVDecide.Normalize.BitVec.getElem_eq_getLsbD,
  ]
  for name in relevantNames do
    lemmas := lemmas.insert (← Sym.Simp.mkTheoremFromDecl name)

  return { methods with pre := methods.pre >> lemmas.rewrite }

structure Context where
  /--
  Whether the user restricted the analysis to a fixed set of types through a `types` clause. In that
  case the interesting structures and enums are seeded upfront and the analysis only discovers
  matchers on top of them.
  -/
  restricted : Bool

abbrev AnalysisM := ReaderT Context PreProcessM

public partial def typeAnalysisPass : Pass where
  name := `typeAnalysis
  run' := do
    let restrictedTypes ← PreProcessM.getRestrictedTypes
    if let some types := restrictedTypes then
      seedRestrictedTypes types
    checkContext (← PreProcessM.getTargetMVarId) |>.run { restricted := restrictedTypes.isSome }
    let analysis ← PreProcessM.getTypeAnalysis
    trace[Meta.Tactic.bv] m!"Type analysis found structures: {analysis.interestingStructures.toList}"
    trace[Meta.Tactic.bv] m!"Type analysis found enums: {analysis.interestingEnums.toList}"
    trace[Meta.Tactic.bv] m!"Type analysis found matchers: {analysis.interestingMatchers.keys}"
    return false
where
  seedRestrictedTypes (types : Array Name) : PreProcessM Unit := do
    for type in types do
      if ← isEnumType type then
        PreProcessM.markInterestingEnum type
      else if isStructure (← getEnv) type then
        PreProcessM.markInterestingStructure type
      else
        throwError "`{type}` is neither a structure nor an enum inductive"

  checkContext (goal : MVarId) : AnalysisM Unit := do
    goal.withContext do
      for decl in ← getLCtx do
        if !decl.isLet && !decl.isImplementationDetail then
          if ← Meta.isProp decl.type then continue
          analyzeType (← Sym.instantiateMVarsS decl.type)

      for hyp in ← PreProcessM.getHyps do
        analyzeType hyp.type

  analyzeType (expr : Expr) : AnalysisM Unit := do
    expr.forEachWhere Expr.isConst fun e => do
      let .const declName .. := e | unreachable!
      discard <| analyzeConst declName

  /--
  Returns true if the const is something that we would like to see revealed by case splitting on
  structures that contain it.
  -/
  analyzeConst (n : Name) : AnalysisM Bool := do
    if isBuiltIn n then return true

    let analysis ← PreProcessM.getTypeAnalysis
    if analysis.interestingStructures.contains n || analysis.interestingEnums.contains n then
      return true
    else if analysis.uninteresting.contains n || analysis.interestingMatchers.contains n then
      return false

    -- Matchers are discovered even in a restricted run as they may discriminate on one of the enums
    -- that we were told to use.
    if let some kind ← isSupportedMatch n then
      let restricted := (← read).restricted
      if !restricted || analysis.interestingEnums.contains kind.getEnumInfo.name then
        PreProcessM.markInterestingMatcher n kind
      else
        PreProcessM.markUninterestingConst n
      return false
    else if (← read).restricted then
      PreProcessM.markUninterestingConst n
      return false
    else if isStructure (← getEnv) n then
      if ← analyzeStructure n then
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

  /--
  Returns true if the structure is appropriate for case splitting and contains fields of interest.
  -/
  analyzeStructure (n : Name) : AnalysisM Bool := do
    let constInfo ← getConstInfoInduct n
    if constInfo.isRec then
      return false

    let ctorTyp := (← getConstInfoCtor constInfo.ctors.head!).type
    let interesting ← forallTelescope ctorTyp fun args _ =>
      -- Note: Important not to short circuit here so that we collect information about all
      -- arguments in case we want to split recursively.
      args.foldlM (init := false) fun state arg => do
        return state || (← typeCasesRelevant (← arg.fvarId!.getType))
    return interesting

  typeCasesRelevant (expr : Expr) : AnalysisM Bool := do
    let some const := expr.getAppFn.constName? | return false
    analyzeConst const

end Normalize
end Lean.Meta.Tactic.BVDecide
