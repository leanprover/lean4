/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.Basic

/-!
This module contains code common to mutual-via-fixedpoint constructions, i.e.
well-founded recursion and partial fixed-points, but independent of the details of the mutual packing.
-/

namespace Lean.Elab.Mutual
open Meta

partial def withCommonTelescope (preDefs : Array PreDefinition) (k : Array Expr → Array Expr → MetaM α) : MetaM α :=
  go #[] (preDefs.map (·.value))
where
  go (fvars : Array Expr) (vals : Array Expr) : MetaM α := do
    if !(vals.all fun val => val.isLambda) then
      k fvars vals
    else if !(← vals.allM fun val => isDefEq val.bindingDomain! vals[0]!.bindingDomain!) then
      k fvars vals
    else
      withLocalDecl vals[0]!.bindingName! vals[0]!.binderInfo vals[0]!.bindingDomain! fun x =>
        go (fvars.push x) (vals.map fun val => val.bindingBody!.instantiate1 x)


/--
* `graph[funIdx][paramIdx] = none`: paramIdx is not fixed
* `graph[funIdx][paramIdx] = some a`:
   * paramIdx is (maybe) fixed, and
   * `a[callerIdx] = none`: we do not yet know to which parameter of `callerIdx` this corresponds
   * `a[callerIdx] = some callerParamIdx`: this param correponds to that param of `callerIdx`
-/
abbrev Info := Array (Array (Option (Array (Option Nat))))

def Info.init (arities : Array Nat) : Info :=
  arities.map fun calleeArity =>
    mkArray calleeArity (some (mkArray arities.size none))

def Info.addSelfCalls (info : Info) : Info :=
  info.mapIdx fun funIdx paramInfos =>
    paramInfos.mapIdx fun paramIdx paramInfo? =>
      paramInfo?.map fun callers =>
        callers.set! funIdx (some paramIdx)

/-- All paremeters known to be non-fixed? Then we can stop. -/
def Info.allNotFixed (info : Info) : Bool :=
  info.any (·.all Option.isNone)

/--
Is this parameter still plausibly a fixed parameter?
-/
def Info.mayBeFixed (callerIdx paramIdx : Nat) (info : Info) : Bool :=
  info[callerIdx]![paramIdx]!.isSome

/--
This parameter is not fixed. Set and propagate that information.
-/
partial def Info.setNotFixed (funIdx paramIdx : Nat) (info : Info) : Info := Id.run do
  let mut info : Info := info
  if info.mayBeFixed funIdx paramIdx then
    info := info.modify funIdx (·.set! paramIdx none)
    for otherFunIdx in [:info.size] do
      for otherParamIdx in [:info[otherFunIdx]!.size] do
        if let some otherParamInfo := info[otherFunIdx]![otherParamIdx]! then
          if otherParamInfo[funIdx]! = some paramIdx then
            info := Info.setNotFixed otherFunIdx otherParamIdx info
  info

def Info.getCallerParam? (calleeIdx argIdx callerIdx : Nat) (info : Info) : Option Nat :=
  info[calleeIdx]![argIdx]!.bind (·[callerIdx]!)

/--
We observe a possibly valid edge.
-/
partial def Info.setCallerParam (calleeIdx argIdx callerIdx paramIdx : Nat) (info : Info) : Info :=
  if info.mayBeFixed calleeIdx argIdx then
    if info.mayBeFixed callerIdx paramIdx then
      if let some paramIdx' := info.getCallerParam? calleeIdx argIdx callerIdx then
      -- We already have an etry
      if paramIdx = paramIdx' then
        -- all good
        info
      else
        -- Inconsistent information, mark both as not fixed
        info.setNotFixed callerIdx paramIdx |>.setNotFixed calleeIdx argIdx
    else
      -- Set the new entry
      let info := info.modify calleeIdx (·.modify argIdx (·.map (·.set! callerIdx (some paramIdx))))
      Id.run do
        -- Propagate
        let mut info : Info := info
        if let some callerParamInfo := info[callerIdx]![paramIdx]! then
          for h : otherFunIdx in [:callerParamInfo.size] do
            if let some otherParamIdx := callerParamInfo[otherFunIdx] then
              info := info.setCallerParam calleeIdx argIdx otherFunIdx otherParamIdx
        return info
    else
      -- Param not fixed, so argument isn't either
      info.setNotFixed calleeIdx argIdx
  else
    info

def getFixedParamsInfo (preDefs : Array PreDefinition) : MetaM Info := do
  let arities ← preDefs.mapM fun preDef => lambdaTelescope preDef.value fun xs _ => pure xs.size
  let ref ← IO.mkRef (Info.init arities)
  ref.modify .addSelfCalls

  for h : callerIdx in [:preDefs.size] do
    let preDef := preDefs[callerIdx]
    lambdaTelescope preDef.value fun params body => do
      assert! params.size = arities[callerIdx]!
      if (← ref.get).allNotFixed then return
      -- TODO: transform is overkill, a simple visit-all-subexpression that takes applications
      -- as whole suffices
      discard <| Meta.transform (skipConstInApp := true) body fun e => e.withApp fun f args => do
        unless f.isConst do
          return .continue
        let n := f.constName!
        let some calleeIdx := preDefs.findIdx? (·.declName = n) | return .continue
        for argIdx in [:arities[calleeIdx]!] do
          if (← ref.get).mayBeFixed calleeIdx argIdx then
            if h : argIdx < args.size then
              let arg := args[argIdx]
              -- We have seen this before (or it is a self-call), so only check that one param
              if let some paramIdx := (← ref.get).getCallerParam? calleeIdx argIdx callerIdx then
                let param := params[paramIdx]!
                unless (← withoutProofIrrelevance <| withReducible <| isDefEq param arg) do
                  trace[Elab.definition.fixedParams] "getFixedParams: notFixed {calleeIdx} {argIdx}:\nIn {e}\n{param} =/= {arg}"
                  ref.modify (Info.setNotFixed calleeIdx argIdx)
              else
              -- Try all parameters
              let mut any := false
              for h : paramIdx in [:params.size] do
                if (← ref.get).mayBeFixed callerIdx paramIdx then
                  let param := params[paramIdx]
                  if (← withoutProofIrrelevance <| withReducible <| isDefEq param arg) then
                    ref.modify (Info.setCallerParam calleeIdx argIdx callerIdx paramIdx)
                    any := true
              unless any do
                trace[Elab.definition.fixedParams] "getFixedParams: notFixed {calleeIdx} {argIdx}:\nIn {e}\n{arg} not matched"
                -- Argument is none of the plausible parameters, so it cannot be a fixed argument
                ref.modify (Info.setNotFixed calleeIdx argIdx)
            else
              -- Underapplication
              trace[Elab.definition.fixedParams] "getFixedParams: notFixed {calleeIdx} {argIdx}:\nIn {e}\ntoo few arguments for {argIdx}"
              ref.modify (Info.setNotFixed calleeIdx argIdx)
        return .continue

  let info ← ref.get
  trace[Elab.definition.fixedParams] "getFixedParams: {info}"
  return info

structure FixedParams where
  /-- A telescope (nested `.lamE` with a dummy body) representing the fixed parameters. -/
  telescope : Expr
  /-- For each function in the clique, a mapping from its parameters to the fixed parameters -/
  mappings : Array (Array (Option Nat))

def getFixedParams (preDefs : Array PreDefinition) : MetaM FixedParams := do
  let info ← getFixedParamsInfo preDefs

  lambdaTelescope preDefs[0]!.value fun xs _ => do
    let paramInfos := info[0]!
    assert! xs.size = paramInfos.size

    let mut ys := #[]
    let mut firstMapping := #[]
    for paramIdx in [:xs.size], x in xs, paramInfo? in paramInfos do
      if let some paramInfo := paramInfo? then
        assert! paramInfo[0]! = some paramIdx
        firstMapping := firstMapping.push (some ys.size)
        ys := ys.push x
      else
        firstMapping := firstMapping.push none
    let telescope ← mkLambdaFVars ys (.sort 0)

    let mut mappings := #[firstMapping]
    for h : funIdx in [1:info.size] do
      let paramInfos := info[funIdx]
      let mut mapping := #[]
      for paramInfo? in paramInfos do
        if let some paramInfo := paramInfo? then
          if let some firstParamIdx := paramInfo[0]! then
            assert! firstMapping[firstParamIdx]!.isSome
            mapping := mapping.push firstMapping[firstParamIdx]!
          else
            panic! "Incomplete paramInfo"
        else
          mapping := mapping.push none
      mappings := mappings.push mapping

    return { telescope, mappings }


def checkFixedParams (preDefs : Array PreDefinition) (fixedPrefixSize : Nat) : MetaM Unit := do
  let fixedParams ← getFixedParams preDefs
  for preDef in preDefs, mapping in fixedParams.mappings do
    unless mapping[:fixedPrefixSize] = (Array.range fixedPrefixSize).map Option.some do
      throwError "Fixed prefix mismatch for {preDef.declName}: Expeted {fixedPrefixSize}, but got {mapping}"

def getFixedPrefix (preDefs : Array PreDefinition) : MetaM Nat :=
  withCommonTelescope preDefs fun xs vals => do
    let resultRef ← IO.mkRef xs.size
    for val in vals do
      if (← resultRef.get) == 0 then return 0
      forEachExpr' val fun e => do
        if preDefs.any fun preDef => e.isAppOf preDef.declName then
          let args := e.getAppArgs
          resultRef.modify (min args.size ·)
          for arg in args, x in xs do
            if !(← withoutProofIrrelevance <| withReducible <| isDefEq arg x) then
              -- We continue searching if e's arguments are not a prefix of `xs`
              return true
          return false
        else
          return true
    let fixedPrefixSize ← resultRef.get
    checkFixedParams preDefs fixedPrefixSize
    return fixedPrefixSize

def addPreDefsFromUnary (preDefs : Array PreDefinition) (preDefsNonrec : Array PreDefinition)
    (unaryPreDefNonRec : PreDefinition) : TermElabM Unit := do
  /-
  We must remove `implemented_by` attributes from the auxiliary application because
  this attribute is only relevant for code that is compiled. Moreover, the `[implemented_by <decl>]`
  attribute would check whether the `unaryPreDef` type matches with `<decl>`'s type, and produce
  and error. See issue #2899
  -/
  let preDefNonRec := unaryPreDefNonRec.filterAttrs fun attr => attr.name != `implemented_by
  let declNames := preDefs.toList.map (·.declName)

  -- Do not complain if the user sets @[semireducible], which usually is a noop,
  -- we recognize that below and then do not set @[irreducible]
  withOptions (allowUnsafeReducibility.set · true) do
    if unaryPreDefNonRec.declName = preDefs[0]!.declName then
      addNonRec preDefNonRec (applyAttrAfterCompilation := false)
    else
      withEnableInfoTree false do
        addNonRec preDefNonRec (applyAttrAfterCompilation := false)
      preDefsNonrec.forM (addNonRec · (applyAttrAfterCompilation := false) (all := declNames))

/--
Cleans the right-hand-sides of the predefinitions, to prepare for inclusion in the EqnInfos:
 * Remove RecAppSyntax markers
 * Abstracts nested proofs (and for that, add the `_unsafe_rec` definitions)
-/
def cleanPreDefs (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) := do
  addAndCompilePartialRec preDefs
  let preDefs ← preDefs.mapM (eraseRecAppSyntax ·)
  let preDefs ← preDefs.mapM (abstractNestedProofs ·)
  return preDefs

/--
Assign final attributes to the definitions. Assumes the EqnInfos to be already present.
-/
def addPreDefAttributes (preDefs : Array PreDefinition) : TermElabM Unit := do
  for preDef in preDefs do
    markAsRecursive preDef.declName
    generateEagerEqns preDef.declName
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation
    -- Unless the user asks for something else, mark the definition as irreducible
    unless preDef.modifiers.attrs.any fun a =>
      a.name = `reducible || a.name = `semireducible do
      setIrreducibleAttribute preDef.declName

end Lean.Elab.Mutual

builtin_initialize
  Lean.registerTraceClass `Elab.definition.fixedParams
