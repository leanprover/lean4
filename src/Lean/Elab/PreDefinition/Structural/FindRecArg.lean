/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.TerminationMeasure
import Lean.Elab.PreDefinition.FixedParams
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Elab.PreDefinition.Structural.RecArgInfo

namespace Lean.Elab.Structural
open Meta

def prettyParam (xs : Array Expr) (i : Nat) : MetaM MessageData := do
  let x := xs[i]!
  let n ← x.fvarId!.getUserName
  addMessageContextFull <| if n.hasMacroScopes then m!"#{i+1}" else m!"{x}"

def prettyRecArg (xs : Array Expr) (value : Expr) (recArgInfo : RecArgInfo) : MetaM MessageData := do
  lambdaTelescope value fun ys _ => prettyParam (xs ++ ys) recArgInfo.recArgPos

def prettyParameterSet (fnNames : Array Name) (xs : Array Expr) (values : Array Expr)
    (recArgInfos : Array RecArgInfo) : MetaM MessageData := do
  if fnNames.size = 1 then
    return m!"parameter " ++ (← prettyRecArg xs values[0]! recArgInfos[0]!)
  else
    let mut l := #[]
    for fnName in fnNames, value in values, recArgInfo in recArgInfos do
      l := l.push m!"{(← prettyRecArg xs value recArgInfo)} of {fnName}"
    return m!"parameters " ++ .andList l.toList

private def getIndexMinPos (xs : Array Expr) (indices : Array Expr) : Nat := Id.run do
  let mut minPos := xs.size
  for index in indices do
    match xs.idxOf? index with
    | some pos => if pos < minPos then minPos := pos
    | _        => pure ()
  return minPos

-- Indices can only depend on other indices
private def hasBadIndexDep? (ys : Array Expr) (indices : Array Expr) : MetaM (Option (Expr × Expr)) := do
  for index in indices do
    let indexType ← inferType index
    for y in ys do
      if !indices.contains y && (← dependsOn indexType y.fvarId!) then
        return some (index, y)
  return none

-- Inductive datatype parameters cannot depend on ys
private def hasBadParamDep? (ys : Array Expr) (indParams : Array Expr) : MetaM (Option (Expr × Expr)) := do
  for p in indParams do
    for y in ys do
      if ← dependsOn p y.fvarId! then
        return some (p, y)
  return none

/--
Assemble the `RecArgInfo` for the `i`th parameter in the parameter list `xs`. This performs
various sanity checks on the parameter (is it even of inductive type etc).
-/
def getRecArgInfo (fnName : Name) (fixedParamPerm : FixedParamPerm) (xs : Array Expr) (i : Nat) : MetaM RecArgInfo := do
  assert! fixedParamPerm.size = xs.size
  if h : i < xs.size then
    if fixedParamPerm.isFixed i then
      throwError "it is unchanged in the recursive calls"
    let x := xs[i]
    let localDecl ← getFVarLocalDecl x
    if localDecl.isLet then
      throwError "it is a let-binding"
    let xType ← whnfD localDecl.type
    matchConstInduct xType.getAppFn (fun _ => throwError "its type is not an inductive") fun indInfo us => do
    if indInfo.isReflexive && !(← hasConst (mkBInductionOnName indInfo.name)) && !(← isInductivePredicate indInfo.name) then
      throwError "its type {indInfo.name} is a reflexive inductive, but {mkBInductionOnName indInfo.name} does not exist and it is not an inductive predicate"
    else
      let indArgs    : Array Expr := xType.getAppArgs
      let indParams  : Array Expr := indArgs[0:indInfo.numParams]
      let indIndices : Array Expr := indArgs[indInfo.numParams:]
      if !indIndices.all Expr.isFVar then
        throwError "its type {indInfo.name} is an inductive family and indices are not variables{indentExpr xType}"
      else if !indIndices.allDiff then
        throwError "its type {indInfo.name} is an inductive family and indices are not pairwise distinct{indentExpr xType}"
      else
        let ys := fixedParamPerm.pickVarying xs
        match (← hasBadIndexDep? ys indIndices) with
        | some (index, y) =>
          throwError "its type {indInfo.name} is an inductive family{indentExpr xType}\nand index{indentExpr index}\ndepends on the non index{indentExpr y}"
        | none =>
          match (← hasBadParamDep? ys indParams) with
          | some (indParam, y) =>
            throwError "its type is an inductive datatype{indentExpr xType}\nand the datatype parameter{indentExpr indParam}\ndepends on the function parameter{indentExpr y}\nwhich is not fixed."
          | none =>
            let indAll := indInfo.all.toArray
            let .some indIdx := indAll.idxOf? indInfo.name | panic! "{indInfo.name} not in {indInfo.all}"
            let indicesPos := indIndices.map fun index => match xs.idxOf? index with | some i => i | none => unreachable!
            let indGroupInst := {
              IndGroupInfo.ofInductiveVal indInfo with
              levels := us
              params := indParams }
            return { fnName       := fnName
                     fixedParamPerm := fixedParamPerm
                     recArgPos    := i
                     indicesPos   := indicesPos
                     indGroupInst := indGroupInst
                     indIdx       := indIdx }
    else
      throwError "the index #{i+1} exceeds {xs.size}, the number of parameters"

/--
Collects the `RecArgInfos` for one function, and returns a report for why the others were not
considered.

The `xs` are the fixed parameters, `value` the body with the fixed prefix instantiated.

Takes the optional user annotation into account (`termMeasure?`). If this is given and the measure
is unsuitable, throw an error.
-/
def getRecArgInfos (fnName : Name) (fixedParamPerm : FixedParamPerm) (xs : Array Expr)
    (value : Expr) (termMeasure? : Option TerminationMeasure) : MetaM (Array RecArgInfo × MessageData) := do
  lambdaTelescope value fun ys _ => do
    if let .some termMeasure := termMeasure? then
      -- User explicitly asked to use a certain measure, so throw errors eagerly
      let recArgInfo ← withRef termMeasure.ref do
        mapError (f := (m!"cannot use specified measure for structural recursion:{indentD ·}")) do
          let args := fixedParamPerm.buildArgs xs ys
          getRecArgInfo fnName fixedParamPerm args (← termMeasure.structuralArg)
      return (#[recArgInfo], m!"")
    else
      let args := fixedParamPerm.buildArgs xs ys
      let mut recArgInfos := #[]
      let mut report : MessageData := m!""
      -- No `termination_by`, so try all, and remember the errors
      for idx in [:args.size] do
        try
          let recArgInfo ← getRecArgInfo fnName fixedParamPerm args idx
          recArgInfos := recArgInfos.push recArgInfo
        catch e =>
          report := report ++ (m!"Not considering parameter {← prettyParam args idx} of {fnName}:" ++
            indentD e.toMessageData) ++ "\n"
      trace[Elab.definition.structural] "getRecArgInfos report: {report}"
      return (recArgInfos, report)


/--
Reorders the `RecArgInfos` of one function to put arguments that are indices of other arguments
last.
See issue #837 for an example where we can show termination using the index of an inductive family, but
we don't get the desired definitional equalities.
-/
def nonIndicesFirst (recArgInfos : Array RecArgInfo) : Array RecArgInfo := Id.run do
  let mut indicesPos : Std.HashSet Nat := {}
  for recArgInfo in recArgInfos do
    for pos in recArgInfo.indicesPos do
      indicesPos := indicesPos.insert pos
  let (indices,nonIndices) := recArgInfos.partition (indicesPos.contains ·.recArgPos)
  return nonIndices ++ indices

private def dedup [Monad m] (eq : α → α → m Bool) (xs : Array α) : m (Array α) := do
  let mut ret := #[]
  for x in xs do
    unless (← ret.anyM (eq · x)) do
      ret := ret.push x
  return ret

/--
Given the `RecArgInfo`s of all the recursive functions, find the inductive groups to consider.
-/
def inductiveGroups (recArgInfos : Array RecArgInfo) : MetaM (Array IndGroupInst) :=
  dedup IndGroupInst.isDefEq (recArgInfos.map (·.indGroupInst))

/--
Filters the `recArgInfos` by those that describe an argument that's part of the recursive inductive
group `group`.

Because of nested inductives this function has the ability to change the `recArgInfo`.
Consider
```
inductive Tree where | node : List Tree → Tree
```
then when we look for arguments whose type is part of the group `Tree`, we want to also consider
the argument of type `List Tree`, even though that argument’s `RecArgInfo` refers to initially to
`List`.
-/
def argsInGroup (group : IndGroupInst) (xs : Array Expr) (value : Expr)
    (recArgInfos : Array RecArgInfo) : MetaM (Array RecArgInfo) := do

  let nestedTypeFormers ← group.nestedTypeFormers

  recArgInfos.filterMapM fun recArgInfo => do
    -- Is this argument from the same mutual group of inductives?
    if (← group.isDefEq recArgInfo.indGroupInst) then
      return (.some recArgInfo)

    -- Can this argument be understood as the auxiliary type former of a nested inductive?
    if nestedTypeFormers.isEmpty then return .none
    lambdaTelescope value fun ys _ => do
      let x := (xs++ys)[recArgInfo.recArgPos]!
      for nestedTypeFormer in nestedTypeFormers, indIdx in [group.all.size : group.numMotives] do
        let xType ← whnfD (← inferType x)
        let (indIndices, _, type) ← forallMetaTelescope nestedTypeFormer
        if (← isDefEqGuarded type xType) then
          let indIndices ← indIndices.mapM instantiateMVars
          if !indIndices.all Expr.isFVar then
            -- throwError "indices are not variables{indentExpr xType}"
            continue
          if !indIndices.allDiff then
            -- throwError "indices are not pairwise distinct{indentExpr xType}"
            continue
          -- TODO: Do we have to worry about the indices ending up in the fixed prefix here?
          if let some (_index, _y) ← hasBadIndexDep? ys indIndices then
            -- throwError "its type {indInfo.name} is an inductive family{indentExpr xType}\nand index{indentExpr index}\ndepends on the non index{indentExpr y}"
            continue
          let indicesPos := indIndices.map fun index => match (xs++ys).idxOf? index with | some i => i | none => unreachable!
          return .some
            { fnName       := recArgInfo.fnName
              fixedParamPerm  := recArgInfo.fixedParamPerm
              recArgPos    := recArgInfo.recArgPos
              indicesPos   := indicesPos
              indGroupInst := group
              indIdx       := indIdx }
      return .none

def maxCombinationSize : Nat := 10

def allCombinations (xss : Array (Array α)) : Option (Array (Array α)) :=
  if xss.foldl (· * ·.size) 1 > maxCombinationSize then
    none
  else
    let rec go i acc : Array (Array α):=
      if h : i < xss.size then
        xss[i].flatMap fun x => go (i + 1) (acc.push x)
      else
        #[acc]
    some (go 0 #[])


def tryAllArgs (fnNames : Array Name) (fixedParamPerms : FixedParamPerms) (xs : Array Expr)
   (values : Array Expr) (termMeasure?s : Array (Option TerminationMeasure)) (k : Array RecArgInfo → M α) : M α := do
  let mut report := m!""
  -- Gather information on all possible recursive arguments
  let mut recArgInfoss := #[]
  for fnName in fnNames, value in values, termMeasure? in termMeasure?s, fixedParamPerm in fixedParamPerms.perms do
    let (recArgInfos, thisReport) ← getRecArgInfos fnName fixedParamPerm xs value termMeasure?
    report := report ++ thisReport
    recArgInfoss := recArgInfoss.push recArgInfos
  -- Put non-indices first
  recArgInfoss := recArgInfoss.map nonIndicesFirst
  trace[Elab.definition.structural] "recArgInfos:{indentD (.joinSep (recArgInfoss.flatten.toList.map (repr ·)) Format.line)}"
  -- Inductive groups to consider
  let groups ← inductiveGroups recArgInfoss.flatten
  trace[Elab.definition.structural] "inductive groups: {groups}"
  if groups.isEmpty then
    report := report ++ "no parameters suitable for structural recursion"
  -- Consider each group
  for group in groups do
    -- Select those RecArgInfos that are compatible with this inductive group
    let mut recArgInfoss' := #[]
    for value in values, recArgInfos in recArgInfoss do
      recArgInfoss' := recArgInfoss'.push (← argsInGroup group xs value recArgInfos)
    if let some idx := recArgInfoss'.findIdx? (·.isEmpty) then
      report := report ++ m!"Skipping arguments of type {group}, as {fnNames[idx]!} has no compatible argument.\n"
      continue
    if let some combs := allCombinations recArgInfoss' then
      for comb in combs do
        try
          -- Check that the group actually has a brecOn (we used to check this in getRecArgInfo,
          -- but in the first phase we do not want to rule-out non-recursive types like `Array`, which
          -- are ok in a nested group. This logic can maybe simplified)
          unless (← hasConst (group.brecOnName false 0)) do
            throwError "the type {group} does not have a `.brecOn` recursor"
          let r ← k comb
          trace[Elab.definition.structural] "tryAllArgs report:\n{report}"
          return r
        catch e =>
          let m ← prettyParameterSet fnNames xs values comb
          report := report ++ m!"Cannot use {m}:{indentD e.toMessageData}\n"
    else
          report := report ++ m!"Too many possible combinations of parameters of type {group} (or " ++
            m!"please indicate the recursive argument explicitly using `termination_by structural`).\n"
  report := m!"failed to infer structural recursion:\n" ++ report
  trace[Elab.definition.structural] "tryAllArgs:\n{report}"
  throwError report

end Lean.Elab.Structural
