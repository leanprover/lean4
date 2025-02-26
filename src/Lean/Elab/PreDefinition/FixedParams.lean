/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Elab.PreDefinition.Basic

/-!
This module contains the logic for figuring out, given mutually recursive predefinitions,
which parameters are “fixed”. This used to be a simple task when we only considered a fixed prefix,
but becomes a quite involved task if we allow fixed parameters also later in the parameter list,
and possibly in a different order in different modules.

The main components of this module are

 * The pure `Info` data type for the bookkeeping during analysis
 * The `FixedParams` data type, a projection of `Info`, with the analysis result.
 * The `getFixedParams` function that calculates the fixed parameters
 * Variuos `MetaM` functions for bringing into scope fixed and varying paramters, assembling
   argument lists etc.

-/

namespace Lean.Elab.FixedParams


/--
To determine which parameters in mutually recursive predefinitions are fixed, and how they
correspond to each other, we run an analysis that aggregates information in the `Info` data type.

Abstractly, this represents
* a set `varying` of `(funIdx × paramIdx)` pairs known to be varying, initially empty
* a directed graph whose nodes are `(funIdx × paramIdx)` pairs, initially empty

We find the largest set and graph that satisfies these rules:
* Every parameter has to be related to itself: `(funIdx, paramIdx) → (funIdx, paramIdx)`.
* whenever the function with index `caller` calls `callee` and the `argIdx`'s argument is reducibly
  defeq to `paramIdx`, then we have an edge `(caller, paramIdx) → (callee, argIdx)`.
* whenever the function with index `caller` calls `callee` and the `argIdx`'s argument is not reducibly
  defeq to any of the `caller`'s parameters, then `(callee, argIdx) ∈ varying`.
* If we have `(caller, paramIdx₁) → (callee, argIdx)` and `(caller, paramIdx₂) → (callee, argIdx)`
  with `paramIdx₁ ≠ paramIdx₂`, then `(callee, argIdx) ∈ varying`.
* The graph is transitive
* If we have `(caller, paramIdx) → (callee, argIdx)` and `(caller, paramIdx) ∈ varying`, then
  `(callee, argIdx) ∈ varying`
* If the type of `funIdx`’s parameter `paramIdx₂ depends on the `paramIdx₁` and
  `(funIdx, paramIdx₁) ∈ varying`, then `(funIdx, paramIdx₁) ∈ varying`
* For structural recursion: The target and all its indices are `varying`. (TODO)

Under the assumption that the predefintions indeed are mutually recursive, then the resulting graph,
restricted to the non-`varying` nodes, should partition into cliques that have one member from each
function. Every such clique becomes a fixed parameter.

-/
structure Info where
  /-
  The concrete data structure for set and graph exploits some of the invariants:
  * Once we know a parameter is varying, it's incoming edges are irrelevant.
  * There can be at most one incoming edge

  So we have

  * `graph[callee][argIdx] = none`: `(callee, argIdx) ∈ varying`
  * `graph[callee][argIdx] = some a`:
    * `(callee, argIdx) ∉ varying` (yet) and
    * `a[callerIdx] = none`: we have no edge to `(callee, argIdx)`
    * `a[callerIdx] = some paramIdx`: we have edge `(callerIdx, paramIdx) → (callee, argIdx)`
  -/
  graph : Array (Array (Option (Array (Option Nat))))
  /--
  The dependency structure of the function parameter.
  If `paramIdx₂ ∈ revDeps[funIdx][paraIdx₁]`, then the type of `paramIdx₂` depends on `parmaIdx₁`
  -/
  revDeps : Array (Array (Array Nat))


def Info.init (revDeps : Array (Array (Array Nat))) : Info where
  graph := revDeps.map fun deps =>
    mkArray deps.size (some (mkArray revDeps.size none))
  revDeps

def Info.addSelfCalls (info : Info) : Info :=
  { info with graph := info.graph.mapIdx fun funIdx paramInfos =>
    paramInfos.mapIdx fun paramIdx paramInfo? =>
      paramInfo?.map fun callers =>
        callers.set! funIdx (some paramIdx) }

/-- All paremeters known to be non-fixed? Then we can stop. -/
def Info.allNotFixed (info : Info) : Bool :=
  info.graph.any (·.all Option.isNone)

/--
Is this parameter still plausibly a fixed parameter?
-/
def Info.mayBeFixed (callerIdx paramIdx : Nat) (info : Info) : Bool :=
  info.graph[callerIdx]![paramIdx]!.isSome

/--
This parameter is varying. Set and propagate that information.
-/
partial def Info.setVarying (funIdx paramIdx : Nat) (info : Info) : Info := Id.run do
  let mut info : Info := info
  if info.mayBeFixed funIdx paramIdx then
    -- Set this as varying
    info := { info with graph := info.graph.modify funIdx (·.set! paramIdx none) }
    -- Propagate along edges for already observed calls
    for otherFunIdx in [:info.graph.size] do
      for otherParamIdx in [:info.graph[otherFunIdx]!.size] do
        if let some otherParamInfo := info.graph[otherFunIdx]![otherParamIdx]! then
          if otherParamInfo[funIdx]! = some paramIdx then
            info := Info.setVarying otherFunIdx otherParamIdx info
    -- Propagate along type dependencies edges
    for dependingParam in info.revDeps[funIdx]![paramIdx]! do
      info := Info.setVarying funIdx dependingParam info
  info

def Info.getCallerParam? (calleeIdx argIdx callerIdx : Nat) (info : Info) : Option Nat :=
  info.graph[calleeIdx]![argIdx]!.bind (·[callerIdx]!)

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
        -- Inconsistent information
        info.setVarying calleeIdx argIdx
    else
      -- Set the new entry
      let info := { info with graph := info.graph.modify calleeIdx (·.modify argIdx (·.map (·.set! callerIdx (some paramIdx)))) }
      Id.run do
        -- Propagate information about the caller
        let mut info : Info := info
        if let some callerParamInfo := info.graph[callerIdx]![paramIdx]! then
          for h : otherFunIdx in [:callerParamInfo.size] do
            if let some otherParamIdx := callerParamInfo[otherFunIdx] then
              info := info.setCallerParam calleeIdx argIdx otherFunIdx otherParamIdx
        -- Propagate information about the callee
        for otherFunIdx in [:info.graph.size] do
          for otherArgIdx in [:info.graph[otherFunIdx]!.size] do
            if let some otherArgsInfo := info.graph[otherFunIdx]![otherArgIdx]! then
              if let some paramIdx' := otherArgsInfo[calleeIdx]! then
                if paramIdx' = argIdx then
                  info := info.setCallerParam otherFunIdx otherArgIdx callerIdx paramIdx

        return info
    else
      -- Param not fixed, so argument isn't either
      info.setVarying calleeIdx argIdx
  else
    info

def Info.format (info : Info) : Format := Format.line.joinSep <|
  info.graph.toList.map fun paramInfos =>
    (f!"• " ++ ·) <| f!" ".joinSep <| paramInfos.toList.map fun
      | .none => f!"❌"
      | .some callerInfos => .sbracket <| f!" ".joinSep <| callerInfos.toList.map fun
        | Option.none => f!"?"
        | .some idx => f!"#{idx+1}"


instance : ToFormat Info := ⟨Info.format⟩

end FixedParams

open Lean Meta FixedParams

def getParamRevDeps (preDefs : Array PreDefinition) : MetaM (Array (Array (Array Nat))) := do
  preDefs.mapM fun preDef =>
    lambdaTelescope preDef.value (cleanupAnnotations := true) fun xs _ => do
      let mut revDeps := #[]
      for h : i in [:xs.size] do
        let mut deps := #[]
        for h : j in [i+1:xs.size] do
          if (← dependsOn (← inferType xs[j]) xs[i].fvarId!) then
            deps := deps.push j
        revDeps := revDeps.push deps
      pure revDeps

def getFixedParamsInfo (preDefs : Array PreDefinition) : MetaM FixedParams.Info := do
  let revDeps ← getParamRevDeps preDefs
  let arities := revDeps.map (·.size)
  let ref ← IO.mkRef (Info.init revDeps)

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
                  ref.modify (Info.setVarying calleeIdx argIdx)
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
                ref.modify (Info.setVarying calleeIdx argIdx)
            else
              -- Underapplication
              trace[Elab.definition.fixedParams] "getFixedParams: notFixed {calleeIdx} {argIdx}:\nIn {e}\ntoo few arguments for {argIdx}"
              ref.modify (Info.setVarying calleeIdx argIdx)
        return .continue

  let info ← ref.get
  trace[Elab.definition.fixedParams] "getFixedParams:{info.format.indentD}"
  return info


/--
This data structure stores the result of the fixed parameter analysis. See `FixedParams.Info` for
details on the analysis.
-/
structure FixedParams where
  /-- Mumber of fixed parameter -/
  size : Nat
  /-- A telescope (nested `.lamE` with a dummy body) representing the fixed parameters. TODO: Needed?-/
  telescope : Expr
  /-- For each function in the clique, a mapping from its parameters to the fixed parameters -/
  mappings : Array (Array (Option Nat))
deriving Inhabited, Repr

def getFixedParams (preDefs : Array PreDefinition) : MetaM FixedParams := do
  let info ← getFixedParamsInfo preDefs
  lambdaTelescope preDefs[0]!.value fun xs _ => do
    let paramInfos := info.graph[0]!
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
    for h : funIdx in [1:info.graph.size] do
      let paramInfos := info.graph[funIdx]
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
private partial def FixedParams.forallTelescopeImpl (fixedParams : FixedParams) (funIdx : Nat)
    (type : Expr) (k : Array Expr → MetaM α) : MetaM α := do
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
  go 0 type (mkArray fixedParams.size (mkSort 0))
where
  go i type xs := do
    match fixedParams.mappings[funIdx]![i]? with
    | .some (Option.some fixedParamIdx) =>
      forallBoundedTelescope type (some 1) (cleanupAnnotations := true) fun xs' type => do
        assert! xs'.size = 1
        let x := xs'[0]!
        assert! !(← inferType x).hasLooseBVars
        assert! fixedParamIdx < xs.size
        go (i + 1) type (xs.set! fixedParamIdx x)
    | .some .none =>
      let type ← whnf type
      assert! type.isForall
      go (i + 1) type.bindingBody! xs
    | .none =>
      k xs

def FixedParams.forallTelescope [MonadControlT MetaM n] [Monad n]
    (fixedParams : FixedParams) (funIdx : Nat) (type : Expr) (k : Array Expr → n α) : n α := do
  map1MetaM (fun k => FixedParams.forallTelescopeImpl fixedParams funIdx type k) k


/--
If `type` is the type of the `funIdx`'s function, instantiate the fixed paramters.
-/
def FixedParams.instantiateForall (fixedParams : FixedParams) (funIdx : Nat) (type₀ : Expr) (xs : Array Expr) : MetaM Expr := do
  assert! xs.size = fixedParams.size
  let mask := fixedParams.mappings[funIdx]!.toList
  go mask type₀
where
  go | [], type => pure type
     | (.some fixedParamIdx)::mask, type => do
        assert! fixedParamIdx < xs.size
        go mask (← Meta.instantiateForall type #[xs[fixedParamIdx]!])
     | .none::mask, type =>
        forallBoundedTelescope type (some 1) fun ys type => do
          assert! ys.size = 1
          mkForallFVars ys (← go mask type)

/--
If `type` is the body of the `funIdx`'s function, instantiate the fixed paramters.
-/
def FixedParams.instantiateLambda (fixedParams : FixedParams) (funIdx : Nat) (type₀ : Expr) (xs : Array Expr) : MetaM Expr := do
  assert! xs.size = fixedParams.size
  let mask := fixedParams.mappings[funIdx]!.toList
  go mask type₀
where
  go | [], type => pure type
     | (.some fixedParamIdx)::mask, type => do
        assert! fixedParamIdx < xs.size
        go mask (← Meta.instantiateLambda type #[xs[fixedParamIdx]!])
     | .none::mask, type =>
        lambdaBoundedTelescope type 1 fun ys type => do
          assert! ys.size = 1
          mkLambdaFVars ys (← go mask type)

/--
If `xs` are arguments to the `funIdx`'s function, pick only the fixed ones, and retun them in the
canonical order.
-/
def FixedParams.pickFixed (fixedParams : FixedParams) (funIdx : Nat) (xs : Array α) : Array α := Id.run do
  let mask := fixedParams.mappings[funIdx]!
  assert! mask.size = xs.size
  if h : xs.size = 0 then
    pure #[]
  else
    let dummy := xs[0]
    let ys := mkArray fixedParams.size dummy
    go (mask.zip xs).toList ys
where
  go | [], ys => return ys
     | (.some fixedParamIdx, x)::xs, ys => do
        assert! fixedParamIdx < ys.size
        go xs (ys.set! fixedParamIdx x)
     | (.none, _) :: mask, ys =>
        go mask ys

/--
If `xs` are arguments to the `funIdx`'s function, pick only the varying ones.
-/
def FixedParams.pickVarying (fixedParams : FixedParams) (funIdx : Nat) (xs : Array α) : Array α := Id.run do
  let mask := fixedParams.mappings[funIdx]!
  assert! mask.size = xs.size
  let mut ys := #[]
  for h : i in [:xs.size] do
    if mask[i]!.isNone then ys := ys.push xs[i]
  pure ys

partial def FixedParams.buildArgs (fixedParams : FixedParams) (funIdx : Nat) (fixedArgs varyingArgs : Array α) : Array α :=
  let mask := fixedParams.mappings[funIdx]!
  assert! fixedArgs.size = fixedParams.size
  assert! mask.size = fixedParams.size + varyingArgs.size
  go mask 0 0 #[]
where
  go mask i j xs :=
    if _ : i < mask.size then
      if let some fixedParamIdx := mask[i] then
        if _ : fixedParamIdx < fixedArgs.size then
          go mask (i + 1) j (xs.push fixedArgs[fixedParamIdx])
        else
          panic! "FixedParams.buildArgs: too few fixed args"
      else
        if _ : j < varyingArgs.size then
          go mask (i + 1) (j + 1) (xs.push varyingArgs[j])
        else
          panic! "FixedParams.buildArgs: too few fixed args"
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

end Lean.Elab

builtin_initialize
  Lean.registerTraceClass `Elab.definition.fixedParams
