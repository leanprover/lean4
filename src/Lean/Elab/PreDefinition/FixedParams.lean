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
 * The `FixedParamPerm` type, with the analysis result for one function
   (effectively a mask and a permutation)
 * The `FixedParamPerms` data type, with the data for a whole recursive group.
 * The `getFixedParamPerms` function that calculates the fixed parameters
 * Various `MetaM` functions for bringing into scope fixed and varying paramters, assembling
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
* For structural recursion: The target and all its indices are `varying`.
  (This is taking into account post-hoc, using `FixedParamPerms.erase`)

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
For a given function, a mapping from its parameters to the (indices of the) fixed parameters of the
recursive group.
The length of the array is the arity of the function, as determined from its body, consistent
with the arity used by well-founded recursion.
For the first function, they appear in order; for other functions they may be reordered.
-/
abbrev FixedParamPerm := Array (Option Nat)

/--
This data structure stores the result of the fixed parameter analysis. See `FixedParams.Info` for
details on the analysis.
-/
structure FixedParamPerms where
  /-- Number of fixed parameters -/
  numFixed : Nat
  /--
  For each function in the clique, a mapping from its parameters to the fixed parameters.
  For the first function, they appear in order; for other functions they may be reordered.
   -/
  perms : Array FixedParamPerm
  /--
  The dependencies among the parameters. See `FixedParams.Info.revDeps`.
  We need this for the `FixedParamsPerm.erase` operation.
  -/
  revDeps : Array (Array (Array Nat))
deriving Inhabited, Repr

def getFixedParamPerms (preDefs : Array PreDefinition) : MetaM FixedParamPerms := do
  let info ← getFixedParamsInfo preDefs
  lambdaTelescope preDefs[0]!.value fun xs _ => do
    let paramInfos := info.graph[0]!
    assert! xs.size = paramInfos.size

    let mut firstPerm := #[]
    let mut numFixed := 0
    for paramIdx in [:xs.size], x in xs, paramInfo? in paramInfos do
      if let some paramInfo := paramInfo? then
        assert! paramInfo[0]! = some paramIdx
        firstPerm := firstPerm.push (some numFixed)
        numFixed := numFixed + 1
      else
        firstPerm := firstPerm.push none

    let mut perms := #[firstPerm]
    for h : funIdx in [1:info.graph.size] do
      let paramInfos := info.graph[funIdx]
      let mut perm := #[]
      for paramInfo? in paramInfos do
        if let some paramInfo := paramInfo? then
          if let some firstParamIdx := paramInfo[0]! then
            assert! firstPerm[firstParamIdx]!.isSome
            perm := perm.push firstPerm[firstParamIdx]!
          else
            panic! "Incomplete paramInfo"
        else
          perm := perm.push none
      perms := perms.push perm

    return { numFixed, perms, revDeps := info.revDeps }

def FixedParamPerm.numFixed (perm : FixedParamPerm) : Nat :=
  perm.countP Option.isSome

def FixedParamPerm.isFixed (perm : FixedParamPerm) (i : Nat) : Bool :=
  perm[i]?.join.isSome

/--
Brings the fixed parameters from `type`, which should the the type of the `funIdx`'s function, into
scope.
-/
private partial def FixedParamPerm.forallTelescopeImpl (perm : FixedParamPerm)
    (type : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  go 0 type (mkArray perm.numFixed (mkSort 0))
where
  go i type xs := do
    match perm[i]? with
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

def FixedParamPerm.forallTelescope [MonadControlT MetaM n] [Monad n]
    (perm : FixedParamPerm) (type : Expr) (k : Array Expr → n α) : n α := do
  map1MetaM (fun k => perm.forallTelescopeImpl type k) k


/--
If `type` is the type of the `funIdx`'s function, instantiate the fixed paramters.
-/
def FixedParamPerm.instantiateForall (perm: FixedParamPerm) (type₀ : Expr) (xs : Array Expr) : MetaM Expr := do
  assert! xs.size = perm.numFixed
  let mask := perm.toList
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
If `value` is the body of the `funIdx`'s function, instantiate the fixed paramters.
Expects enough manifest lambdas to instantiate all fixed parameters, but can handle
eta-contracted definitions beyond that.
-/
def FixedParamPerm.instantiateLambda (perm : FixedParamPerm) (value₀ : Expr) (xs : Array Expr) : MetaM Expr := do
  assert! xs.size = perm.numFixed
  let mask := perm.toList
  go mask value₀
where
  go | [], value => pure value
     | (.some fixedParamIdx)::mask, value => do
        assert! fixedParamIdx < xs.size
        go mask (← Meta.instantiateLambda value #[xs[fixedParamIdx]!])
     | .none::mask, value =>
        if mask.all Option.isNone then
          -- Nothing left to do. Also helpful if we may encounter an eta-contracted value
          return value
        else
          lambdaBoundedTelescope value 1 fun ys value => do
            assert! ys.size = 1
            mkLambdaFVars ys (← go mask value)

/--
If `xs` are arguments to the `funIdx`'s function, pick only the fixed ones, and reorder appropriately.
Expects `xs` to match the arity of the function.
-/
def FixedParamPerm.pickFixed (perm : FixedParamPerm) (xs : Array α) : Array α := Id.run do
  assert! xs.size = perm.size
  if h : xs.size = 0 then
    pure #[]
  else
    let dummy := xs[0]
    let ys := mkArray perm.numFixed dummy
    go (perm.zip xs).toList ys
where
  go | [], ys => return ys
     | (.some fixedParamIdx, x)::xs, ys => do
        assert! fixedParamIdx < ys.size
        go xs (ys.set! fixedParamIdx x)
     | (.none, _) :: perm, ys =>
        go perm ys

/--
If `xs` are arguments to the `funIdx`'s function, pick only the varying ones.
Unlike `pickFixed`, this function can handle over- or under-application.
-/
def FixedParamPerm.pickVarying (perm : FixedParamPerm) (xs : Array α) : Array α := Id.run do
  let mut ys := #[]
  for h : i in [:xs.size] do
    if perm[i]?.join.isNone then ys := ys.push xs[i]
  pure ys

/--
Intersperses the fixed and varying parameters to be in the original parameter order.
Can handle over- or und-application (extra or missing varying args), as long
as there are all varying parameters that go before fixed parameters.
(We expect to always find all fixed parameters, else they woudn't be fixed parameters.)
-/
partial def FixedParamPerm.buildArgs (perm : FixedParamPerm) (fixedArgs varyingArgs : Array α) : Array α :=
  assert! fixedArgs.size = perm.numFixed
  go 0 0 #[]
where
  go i j (xs : Array α) :=
    if _ : i < perm.size then
      if let some fixedParamIdx := perm[i] then
        if _ : fixedParamIdx < fixedArgs.size then
          go (i + 1) j (xs.push fixedArgs[fixedParamIdx])
        else
          panic! "FixedParams.buildArgs: too few fixed args"
      else
        if _ : j < varyingArgs.size then
          go (i + 1) (j + 1) (xs.push varyingArgs[j])
        else
          if perm[i:].all Option.isNone then
            xs -- Under-application
          else
            panic! "FixedParams.buildArgs: too few varying args"
    else
      xs ++ varyingArgs[j:] -- (Possibly) over-application

/--
Are all fixed parameters a non-reordered prefix?
-/
def FixedParamPerms.fixedArePrefix (fixedParamPerms : FixedParamPerms) : Bool :=
  fixedParamPerms.perms.all fun paramInfos =>
    paramInfos ==
      (Array.range fixedParamPerms.numFixed).map Option.some ++
      mkArray (paramInfos.size - fixedParamPerms.numFixed) .none

/--
If `xs` are the fixed parameters that are in scope, and `toErase` are, for each function, the
positions of arguments that must no longer be fixed parameters, then this function splits partitions
`xs` into those to keep and those to erase, and updates `FixedParams` accordingly.

This is used in structural recursion, where we may discover that some fixed parameters are actually
indices and need to be treated as varying, including all parameters that depend on them.
-/
def FixedParamPerms.erase  (fixedParamPerms : FixedParamPerms) (xs : Array Expr)
    (toErase : Array (Array Nat)) : (FixedParamPerms × Array Expr × Array FVarId) := Id.run do
  assert! xs.all (·.isFVar)
  assert! fixedParamPerms.numFixed  = xs.size
  assert! toErase.size = fixedParamPerms.perms.size
  -- Calculate a mask on the fixed parameters of variables to erase
  let mut mask := mkArray fixedParamPerms.numFixed false
  for funIdx in [:toErase.size], paramIdxs in toErase, mapping in fixedParamPerms.perms do
    for paramIdx in paramIdxs do
      assert! paramIdx < mapping.size
      if let some fixedParamIdx := mapping[paramIdx]! then
        mask := mask.set! fixedParamIdx true
  -- Take the transitive closure under under `fixedParamPerms.revDeps`.
  let mut changed := true
  while changed do
    changed := false
    for h : funIdx in [:fixedParamPerms.perms.size] do
      for h : paramIdx₁ in [:fixedParamPerms.perms[funIdx].size] do
        if let some fixedParamIdx₁ := fixedParamPerms.perms[funIdx][paramIdx₁] then
          if mask[fixedParamIdx₁]! then
            for paramIdx₂ in fixedParamPerms.revDeps[funIdx]![paramIdx₁]! do
              if let some fixedParamIdx₂ := fixedParamPerms.perms[funIdx][paramIdx₂]! then
                if !mask[fixedParamIdx₂]! then
                  mask := mask.set! fixedParamIdx₂ true
                  changed := true
  -- Calculate reindexing map, variables to keep, variables to erase
  let mut reindex := #[]
  let mut fvarsToErase :=#[]
  let mut toKeep :=#[]
  for i in [:mask.size], erase in mask, x in xs do
    if erase then
      reindex := reindex.push none
      fvarsToErase := fvarsToErase.push x.fvarId!
    else
      reindex := reindex.push (Option.some toKeep.size)
      toKeep := toKeep.push x
  let fixedParamPerms' : FixedParamPerms := {
    numFixed := toKeep.size
    perms := fixedParamPerms.perms.map (·.map (·.bind (reindex[·]!)))
    revDeps := fixedParamPerms.revDeps
  }
  return (fixedParamPerms', toKeep, fvarsToErase)

end Lean.Elab

builtin_initialize
  Lean.registerTraceClass `Elab.definition.fixedParams
