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
        -- Propagate information about the caller
        let mut info : Info := info
        if let some callerParamInfo := info[callerIdx]![paramIdx]! then
          for h : otherFunIdx in [:callerParamInfo.size] do
            if let some otherParamIdx := callerParamInfo[otherFunIdx] then
              info := info.setCallerParam calleeIdx argIdx otherFunIdx otherParamIdx
        -- Propagate information about the callee
        for otherFunIdx in [:info.size] do
          for otherArgIdx in [:info[otherFunIdx]!.size] do
            if let some otherArgsInfo := info[otherFunIdx]![otherArgIdx]! then
              if let some paramIdx' := otherArgsInfo[calleeIdx]! then
                info := info.setCallerParam otherFunIdx otherArgIdx callerIdx paramIdx

        return info
    else
      -- Param not fixed, so argument isn't either
      info.setNotFixed calleeIdx argIdx
  else
    info

def Info.format (info : Info) : Format := Format.line.joinSep <| info.toList.map fun paramInfos =>
  (f!"• " ++ ·) <| f!" ".joinSep <| paramInfos.toList.map fun
    | .none => f!"❌"
    | .some callerInfos => .sbracket <| f!" ".joinSep <| callerInfos.toList.map fun
      | Option.none => f!"?"
      | .some idx => f!"#{idx+1}"


instance : ToFormat Info := ⟨Info.format⟩


def getFixedParamsInfo (preDefs : Array PreDefinition) : MetaM Info := do
  let arities ← preDefs.mapM fun preDef => lambdaTelescope preDef.value fun xs _ => pure xs.size
  let ref ← IO.mkRef (Info.init arities)
  ref.modify .addSelfCalls

  for h : callerIdx in [:preDefs.size] do
    let preDef := preDefs[callerIdx]
    lambdaTelescope preDef.value fun params body => do
      assert! params.size = arities[callerIdx]!
      -- TODO: Is this a useful shortcut?
      -- if (← ref.get).allNotFixed then return

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
  trace[Elab.definition.fixedParams] "getFixedParams:{info.format.indentD}"
  return info

structure FixedParams where
  /-- Mumber of fixed parameter -/
  size : Nat
  /-- A telescope (nested `.lamE` with a dummy body) representing the fixed parameters. -/
  telescope : Expr
  /-- For each function in the clique, a mapping from its parameters to the fixed parameters -/
  mappings : Array (Array (Option Nat))
deriving Inhabited

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
    let size := ys.size
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

    return { size, telescope, mappings }


/--
Brings the fixed parameters from `type`, which should the the type of the `funIdx`'s function, into
scope.
-/
partial def forallTelescopeFixedParams (fixedParams : FixedParams) (funIdx : Nat) (type : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  /-
  -- Local implementation shortcut:
  -- We just bring all into scope and then remove the ones we didn't want.
  forallBoundedTelescope type (fixedParams.mappings[funIdx]!.size) fun xs _ => do
    assert! xs.size = fixedParams.mappings[funIdx]!.size
    let mut ys := #[]
    let mut zs := #[]
    for x in xs, paramInfo in fixedParams.mappings[funIdx]! do
      -- TODO: Wrong for different order in non-first functions
      if paramInfo.isSome then
        ys := ys.push x
      else
        zs := zs.push x.fvarId!
    assert! ys.size = fixedParams.size
    withErasedFVars zs (k ys)
  -/
  go 0 type #[]
where
  go i type xs := do
    match fixedParams.mappings[funIdx]![i]? with
    | .some (Option.some _) =>
      forallBoundedTelescope type (some 1) fun xs' type => do
        assert! xs'.size = 1
        assert! !(← inferType xs'[0]!).hasLooseBVars
        go (i + 1) type (xs ++ xs')
    | .some .none =>
      let type ← whnf type
      assert! type.isForall
      go (i + 1) type.bindingBody! xs
    | .none =>
      -- TODO: Reorder xs if funIdx is not 0
      k xs


/--
If `type` is the type of the `funIdx`'s function, instantiate the fixed paramters.
-/
def instantiateForallFixedParams (fixedParams : FixedParams) (funIdx : Nat) (type₀ : Expr) (xs : Array Expr) : MetaM Expr := do
  assert! xs.size = fixedParams.size
  let mask := fixedParams.mappings[funIdx]!.toList
  go mask xs.toList type₀
where
  go | [], [], type => pure type
     | [], _, _ => panic! s!"instantiateForallFixedParams: Too many arguments {xs}"
     | .some _::_, [], _ => panic! s!"instantiateForallFixedParams: Too few arguments {xs}"
      -- TODO: Wrong for different order in non-first functions
     | (.some _)::mask, x::xs, type => do
        go mask xs (← instantiateForall type #[x])
     | .none::mask, xs, type =>
        forallBoundedTelescope type (some 1) fun ys type => do
          assert! ys.size = 1
          mkForallFVars ys (← go mask xs type)

/--
If `type` is the body of the `funIdx`'s function, instantiate the fixed paramters.
-/
def instantiateLambdaFixedParams (fixedParams : FixedParams) (funIdx : Nat) (type₀ : Expr) (xs : Array Expr) : MetaM Expr := do
  assert! xs.size = fixedParams.size
  let mask := fixedParams.mappings[funIdx]!.toList
  go mask xs.toList type₀
where
  go | [], [], type => pure type
     | [], _, _ => panic! s!"instantiateLambdaFixedParams: Too many arguments {xs}"
      -- TODO: Wrong for different order in non-first functions
     | .some _::_, [], _ => panic! s!"instantiateLambdaFixedParams: Too few arguments {xs}"
     | (.some _)::mask, x::xs, type => do
        go mask xs (← instantiateLambda type #[x])
     | .none::mask, xs, type =>
        lambdaBoundedTelescope type 1 fun ys type => do
          assert! ys.size = 1
          mkLambdaFVars ys (← go mask xs type)

/--
If `xs` are arguments to the `funIdx`'s function, pick only the fixed ones.
-/
def pickFixedArgs (fixedParams : FixedParams) (funIdx : Nat) (xs : Array Expr) : Array Expr := Id.run do
  let mask := fixedParams.mappings[funIdx]!.map Option.isSome
  assert! mask.size = xs.size
  let mut ys := #[]
  for i in [:xs.size] do
      -- TODO: Wrong for different order in non-first functions
    if mask[i]! then ys := ys.push xs[i]!
  pure ys

/--
If `xs` are arguments to the `funIdx`'s function, pick only the varying ones.
-/
def pickVaryingArgs (fixedParams : FixedParams) (funIdx : Nat) (xs : Array Expr) : Array Expr := Id.run do
  let mask := fixedParams.mappings[funIdx]!.map Option.isSome
  assert! mask.size = xs.size
  let mut ys := #[]
  for i in [:xs.size] do
    if !mask[i]! then ys := ys.push xs[i]!
  pure ys

partial def buildArgs (fixedParams : FixedParams) (funIdx : Nat) (fixedArgs varyingArgs : Array Expr) : Array Expr :=
  let mask := fixedParams.mappings[funIdx]!
  assert! fixedArgs.size = fixedParams.size
  assert! mask.size = fixedParams.size + varyingArgs.size
  go mask 0 0 #[]
where
  go mask i j xs :=
    if _ : i + j < mask.size then
        -- TODO: Wrong for different order in non-first functions
      if mask[i + j].isSome then
        go mask (i + 1) j (xs.push fixedArgs[i]!)
      else
        go mask i (j + 1) (xs.push varyingArgs[j]!)
    else
      xs


/--
Are all fixed parameters a non-reordered prefix?
-/
def FixedParams.fixedArePrefix (fixedParams : FixedParams) : Bool :=
  fixedParams.mappings.all fun paramInfos =>
    paramInfos ==
      (Array.range fixedParams.size).map Option.some ++
      mkArray (paramInfos.size - fixedParams.size) .none

def checkFixedParams (preDefs : Array PreDefinition) (fixedPrefixSize : Nat) : MetaM Unit := do
  let fixedParams ← getFixedParams preDefs
  for preDef in preDefs, mapping in fixedParams.mappings do
    unless mapping[:fixedPrefixSize] = (Array.range fixedPrefixSize).map Option.some do
      throwError "Fixed prefix mismatch for {preDef.declName}: Expeted {fixedPrefixSize}, but got {mapping}"

def getFixedPrefix (preDefs : Array PreDefinition) : MetaM Nat := do
  let fixedPrefixSize ← withCommonTelescope preDefs fun xs vals => do
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
    resultRef.get
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
