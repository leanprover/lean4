/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Elab.PreDefinition.TerminationArgument

namespace Lean.Elab.Structural
open Meta

private def getIndexMinPos (xs : Array Expr) (indices : Array Expr) : Nat := Id.run do
  let mut minPos := xs.size
  for index in indices do
    match xs.indexOf? index with
    | some pos => if pos.val < minPos then minPos := pos.val
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
various sanity checks on the argument (is it even an inductive type etc).
-/
def getRecArgInfo (fnName : Name) (numFixed : Nat) (xs : Array Expr) (i : Nat) : MetaM RecArgInfo := do
  if h : i < xs.size then
    if i < numFixed then
      throwError "it is unchanged in the recursive calls"
    let x := xs[i]
    let localDecl ← getFVarLocalDecl x
    if localDecl.isLet then
      throwError "it is a let-binding"
    let xType ← whnfD localDecl.type
    matchConstInduct xType.getAppFn (fun _ => throwError "its type is not an inductive") fun indInfo us => do
    if !(← hasConst (mkBRecOnName indInfo.name)) then
      throwError "its type {indInfo.name} does not have a recursor"
    else if indInfo.isReflexive && !(← hasConst (mkBInductionOnName indInfo.name)) && !(← isInductivePredicate indInfo.name) then
      throwError "its type {indInfo.name} is a reflexive inductive, but {mkBInductionOnName indInfo.name} does not exist and it is not an inductive predicate"
    else
      let indArgs    : Array Expr := xType.getAppArgs
      let indParams  : Array Expr := indArgs[0:indInfo.numParams]
      let indIndices : Array Expr := indArgs[indInfo.numParams:]
      if !indIndices.all Expr.isFVar then
        throwError "its type {indInfo.name} is an inductive family and indices are not variables{indentExpr xType}"
      else if !indIndices.allDiff then
        throwError " its type {indInfo.name} is an inductive family and indices are not pairwise distinct{indentExpr xType}"
      else
        let indexMinPos := getIndexMinPos xs indIndices
        let numFixed    := if indexMinPos < numFixed then indexMinPos else numFixed
        let ys          := xs[numFixed:]
        match (← hasBadIndexDep? ys indIndices) with
        | some (index, y) =>
          throwError "its type {indInfo.name} is an inductive family{indentExpr xType}\nand index{indentExpr index}\ndepends on the non index{indentExpr y}"
        | none =>
          match (← hasBadParamDep? ys indParams) with
          | some (indParam, y) =>
            throwError "its type is an inductive datatype{indentExpr xType}\nand the datatype parameter{indentExpr indParam}\ndepends on the function parameter{indentExpr y}\nwhich does not come before the varying parameters and before the indices of the recursion parameter."
          | none =>
            let indicesPos := indIndices.map fun index => match xs.indexOf? index with | some i => i.val | none => unreachable!
            return { fnName      := fnName
                     numFixed    := numFixed
                     recArgPos   := i
                     indicesPos  := indicesPos
                     indName     := indInfo.name
                     indLevels   := us
                     indParams   := indParams
                     indAll      := indInfo.all.toArray }
    else
      throwError "the index #{i+1} exceeds {xs.size}, the number of parameters"

/--
Collects the `RecArgInfos` for one function, and returns a report for why the others were not
considered.

The `xs` are the fixed parameters, `value` the body with the fixed prefix instantiated.

Takes the optional user annotations into account (`termArg?`). If this is given and the argument
is unsuitable, throw an error.
-/
def getRecArgInfos (fnName : Name) (xs : Array Expr) (value : Expr)
    (termArg? : Option TerminationArgument) : MetaM (Array RecArgInfo × MessageData) := do
  lambdaTelescope value fun ys _ => do
    if let .some termArg := termArg? then
      -- User explictly asked to use a certain argument, so throw errors eagerly
      let recArgInfo ← withRef termArg.ref do
        mapError (f := (m!"cannot use specified parameter for structural recursion:{indentD ·}")) do
          getRecArgInfo fnName xs.size (xs ++ ys) (← termArg.structuralArg)
      return (#[recArgInfo], m!"")
    else
      let mut recArgInfos := #[]
      let mut report : MessageData := m!""
      -- No `termination_by`, so try all, and remember the errors
      for idx in [:xs.size + ys.size] do
        try
          let recArgInfo ← getRecArgInfo fnName xs.size (xs ++ ys) idx
          recArgInfos := recArgInfos.push recArgInfo
        catch e =>
          report := report ++ (m!"Not considering parameter #{idx} of {fnName}:" ++
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
  let mut indicesPos : HashSet Nat := {}
  for recArgInfo in recArgInfos do
    for pos in recArgInfo.indicesPos do
      indicesPos := indicesPos.insert pos
  let (indices,nonIndices) := recArgInfos.partition (indicesPos.contains ·.recArgPos)
  return nonIndices ++ indices

-- TODO: Maybe simply an Expr?
structure IndGroupInst where
  all    : Array Name
  levels : List Level
  params : Array Expr


def IndGroupInst.ofRecArgInfo (recArgInfo : RecArgInfo) : IndGroupInst :=
  { all := recArgInfo.indAll
    levels := recArgInfo.indLevels
    params := recArgInfo.indParams
  }

def IndGroupInst.isDefEq (igi1 igi2 : IndGroupInst) : MetaM Bool := do
  unless igi1.all[0]! = igi2.all[0]! do return false
  unless igi1.levels.length = igi2.levels.length do return false
  unless (igi1.levels.zip igi2.levels).all (fun (l₁, l₂) => Level.isEquiv l₁ l₂) do return false
  unless igi1.params.size = igi2.params.size do return false
  unless (← (igi1.params.zip igi2.params).allM (fun (e₁, e₂) => isDefEqGuarded e₁ e₂)) do return false
  return true

def IndGroupInst.toMessageData (igi : IndGroupInst) : MessageData :=
  mkAppN (.const igi.all[0]! igi.levels) igi.params

instance : ToMessageData IndGroupInst where
  toMessageData := IndGroupInst.toMessageData

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
  dedup IndGroupInst.isDefEq (recArgInfos.map (.ofRecArgInfo ·))

/--
Filters the `recArgInfos` by those that describe an argument that's part of the recursive inductive
group `group`.


Anticipating support for nested inductives this function has the ability to change the `recArgInfo`.
Consider
```
inductive Tree where | node : List Tree → Tree
```
then when we look for arguments whose type is part of the group `Tree`, we want to also consider
the argument of type `List Tree`, even though that argument’s `RecArgInfo` refers to initially to
`List`.
-/
def argsInGroup (group : IndGroupInst) (_xs : Array Expr) (_value : Expr)
    (recArgInfos : Array RecArgInfo) : MetaM (Array RecArgInfo) := do
  recArgInfos.filterM fun recArgInfo => group.isDefEq (.ofRecArgInfo recArgInfo)

def maxCombinationSize : Nat := 10

def allCombinations (xss : Array (Array α)) : Option (Array (Array α)) :=
  if xss.foldl (· * ·.size) 1 > maxCombinationSize then
    none
  else
    let rec go i acc : Array (Array α):=
      if h : i < xss.size then
        xss[i].concatMap fun x => go (i + 1) (acc.push x)
      else
        #[acc]
    some (go 0 #[])

def prettyRecArg (xs : Array Expr) (value : Expr) (recArgInfo : RecArgInfo) : MetaM MessageData := do
  lambdaTelescope value fun ys _ => do
    let i := recArgInfo.recArgPos
    let x := (xs ++ ys)[i]!
    let n ← x.fvarId!.getUserName
    addMessageContextFull <| if n.hasMacroScopes then m!"#{i+1}" else m!"{x}"

def prettyParameterSet (fnNames : Array Name) (xs : Array Expr) (values : Array Expr)
    (recArgInfos : Array RecArgInfo) : MetaM MessageData := do
  if fnNames.size = 1 then
    return m!"parameter " ++ (← prettyRecArg xs values[0]! recArgInfos[0]!)
  else
    let mut l := #[]
    for fnName in fnNames, value in values, recArgInfo in recArgInfos do
      l := l.push m!"{(← prettyRecArg xs value recArgInfo)} of {fnName}"
    return m!"parameters " ++ .andList l.toList


def tryAllArgs (fnNames : Array Name) (xs : Array Expr) (values : Array Expr)
   (termArg?s : Array (Option TerminationArgument)) (k : Array RecArgInfo → M α) : M α := do
  let mut report := m!""
  -- Gather information on all possible recursive arguments
  let mut recArgInfoss := #[]
  for fnName in fnNames, value in values, termArg? in termArg?s do
    let (recArgInfos, thisReport) ← getRecArgInfos fnName xs value termArg?
    report := report ++ thisReport
    recArgInfoss := recArgInfoss.push recArgInfos
  -- Put non-indices first
  recArgInfoss := recArgInfoss.map nonIndicesFirst
  trace[Elab.definition.structural] "recArgInfoss: {recArgInfoss.map (·.map (·.recArgPos))}"
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
          -- TODO: Here we used to save and restore the state. But should the `try`-`catch`
          -- not suffice?
          let r ← k comb
          trace[Elab.definition.structural] "tryTellArgs report:\n{report}"
          return r
        catch e =>
          let m ← prettyParameterSet fnNames xs values comb
          report := report ++ m!"Cannot use {m}:{indentD e.toMessageData}\n"
    else
          report := report ++ m!"Too many possible combinations of parameters of type {group} (or " ++
            m!"please the recursive argument explicitly using `termination_by structural`).\n"
  report := m!"failed to infer structural recursion:\n" ++ report
  trace[Elab.definition.structural] "tryTellArgs:\n{report}"
  throwError report

end Lean.Elab.Structural
