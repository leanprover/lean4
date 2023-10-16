/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PullFunDecls
import Lean.Compiler.LCNF.FVarUtil
import Lean.Compiler.LCNF.ScopeM
import Lean.Compiler.LCNF.InferType

namespace Lean.Compiler.LCNF

namespace JoinPointFinder

open ScopeM

/--
Info about a join point candidate (a `fun` declaration) during the find phase.
-/
structure CandidateInfo where
  /--
  The arity of the candidate
  -/
  arity : Nat
  /--
  The set of candidates that rely on this candidate to be a join point.
  For a more detailed explanation see the documentation of `find`
  -/
  associated : HashSet FVarId
  deriving Inhabited

/--
The state for the join point candidate finder.
-/
structure FindState where
  /--
  All current join point candidates accessible by their `FVarId`.
  -/
  candidates : HashMap FVarId CandidateInfo := .empty
  /--
  The `FVarId`s of all `fun` declarations that were declared within the
  current `fun`.
  -/
  scope : HashSet FVarId := .empty

abbrev ReplaceCtx := HashMap FVarId Name

abbrev FindM := ReaderT (Option FVarId) StateRefT FindState ScopeM
abbrev ReplaceM := ReaderT ReplaceCtx CompilerM

/--
Attempt to find a join point candidate by its `FVarId`.
-/
private def findCandidate? (fvarId : FVarId) : FindM (Option CandidateInfo) := do
  return (← get).candidates.find? fvarId

/--
Erase a join point candidate as well as all the ones that depend on it
by its `FVarId`, no error is thrown is the candidate does not exist.
-/
private partial def eraseCandidate (fvarId : FVarId) : FindM Unit := do
  if let some info ← findCandidate? fvarId then
    modify (fun state => { state with candidates := state.candidates.erase fvarId })
    info.associated.forM eraseCandidate

/--
Combinator for modifying the candidates in `FindM`.
-/
private def modifyCandidates (f : HashMap FVarId CandidateInfo → HashMap FVarId CandidateInfo) : FindM Unit :=
  modify (fun state => {state with candidates := f state.candidates })

/--
Remove all join point candidates contained in `a`.
-/
private partial def removeCandidatesInArg (a : Arg) : FindM Unit := do
  forFVarM eraseCandidate a

/--
Remove all join point candidates contained in `a`.
-/
private partial def removeCandidatesInLetValue (e : LetValue) : FindM Unit := do
  forFVarM eraseCandidate e

/--
Add a new join point candidate to the state.
-/
private def addCandidate (fvarId : FVarId) (arity : Nat) : FindM Unit := do
  let cinfo := { arity, associated := .empty }
  modifyCandidates (fun cs => cs.insert fvarId cinfo )

/--
Add a new join point dependency from `src` to `dst`.
-/
private def addDependency (src : FVarId) (target : FVarId) : FindM Unit := do
  if let some targetInfo ← findCandidate? target then
    modifyCandidates (fun cs => cs.insert target { targetInfo with associated := targetInfo.associated.insert src })
  else
    eraseCandidate src

/--
Find all `fun` declarations that qualify as a join point, that is:
- are always fully applied
- are always called in tail position

Where a `fun` `f` is in tail position iff it is called as follows:
```
let res := f arg
res
```
The majority (if not all) tail calls will be brought into this form
by the simplifier pass.

Furthermore a `fun` disqualifies as a join point if turning it into a join
point would turn a call to it into an out of scope join point.
This can happen if we have something like:
```
def test (b : Bool) (x y : Nat) : Nat :=
  fun myjp x => Nat.add x (Nat.add x x)
  fun f y =>
    let x := Nat.add y y
    myjp x
  fun f y =>
    let x := Nat.mul y y
    myjp x
  cases b (f x) (g y)
```
`f` and `g` can be detected as a join point right away, however
`myjp` can only ever be detected as a join point after we have established
this. This is because otherwise the calls to `myjp` in `f` and `g` would
produce out of scope join point jumps.
-/
partial def find (decl : Decl) : CompilerM FindState := do
  let (_, candidates) ← go decl.value |>.run none |>.run {} |>.run' {}
  return candidates
where
  go : Code → FindM Unit
  | .let decl k => do
    match k, decl.value with
    | .return valId, .fvar fvarId args =>
      args.forM removeCandidatesInArg
      if let some candidateInfo ← findCandidate? fvarId then
        -- Erase candidate that are not fully applied or applied outside of tail position
        if valId != decl.fvarId || args.size != candidateInfo.arity then
          eraseCandidate fvarId
        -- Out of scope join point candidate handling
        else if let some upperCandidate ← read then
          if !(← isInScope fvarId) then
            addDependency fvarId upperCandidate
      else
        eraseCandidate fvarId
    | _, _ =>
      removeCandidatesInLetValue decl.value
      go k
  | .fun decl k => do
    withReader (fun _ => some decl.fvarId) do
      withNewScope do
        go decl.value
    addCandidate decl.fvarId decl.getArity
    addToScope decl.fvarId
    go k
  | .jp decl k => do
    go decl.value
    go k
  | .jmp _ args => args.forM removeCandidatesInArg
  | .return val => eraseCandidate val
  | .cases c => do
    eraseCandidate c.discr
    c.alts.forM (·.forCodeM go)
  | .unreach .. => return ()

/--
Replace all join point candidate `fun` declarations with `jp` ones
and all calls to them with `jmp`s.
-/
partial def replace (decl : Decl) (state : FindState) : CompilerM Decl := do
  let mapper := fun acc cname _ => do return acc.insert cname (← mkFreshJpName)
  let replaceCtx : ReplaceCtx ← state.candidates.foldM (init := .empty) mapper
  let newValue ← go decl.value |>.run replaceCtx
  return { decl with value := newValue }
where
  go (code : Code) : ReplaceM Code := do
    match code with
    | .let decl k =>
      match k, decl.value with
      | .return valId, .fvar fvarId args =>
        if valId == decl.fvarId then
          if (← read).contains fvarId then
            eraseLetDecl decl
            return .jmp fvarId args
          else
            return code
        else
          return code
      | _, _ => return Code.updateLet! code decl (← go k)
    | .fun decl k =>
      if let some replacement := (← read).find? decl.fvarId then
        let newDecl := { decl with
          binderName := replacement,
          value := (← go decl.value)
        }
        modifyLCtx fun lctx => lctx.addFunDecl newDecl
        return .jp newDecl (← go k)
      else
        let newDecl ← decl.updateValue (← go decl.value)
        return Code.updateFun! code newDecl (← go k)
    | .jp decl k =>
       let newDecl ← decl.updateValue (← go decl.value)
       return Code.updateFun! code newDecl (← go k)
    | .cases cs =>
      return Code.updateCases! code cs.resultType cs.discr (← cs.alts.mapM (·.mapCodeM go))
    | .jmp .. | .return .. | .unreach .. =>
      return code

end JoinPointFinder

namespace JoinPointContextExtender

open ScopeM

/--
The context managed by `ExtendM`.
-/
structure ExtendContext where
  /--
  The `FVarId` of the current join point if we are currently inside one.
  -/
  currentJp? : Option FVarId := none
  /--
  The list of valid candidates for extending the context. This will be
  all `let` and `fun` declarations as well as all `jp` parameters up
  until the last `fun` declaration in the tree.
  -/
  candidates : FVarIdSet := {}

/--
The state managed by `ExtendM`.
-/
structure ExtendState where
  /--
  A map from join point `FVarId`s to a respective map from free variables
  to `Param`s. The free variables in this map are the once that the context
  of said join point will be extended by by passing in the respective parameter.
  -/
  fvarMap : HashMap FVarId (HashMap FVarId Param) := {}

/--
The monad for the `extendJoinPointContext` pass.
-/
abbrev ExtendM := ReaderT ExtendContext StateRefT ExtendState ScopeM

/--
Replace a free variable if necessary, that is:
- It is in the list of candidates
- We are currently within a join point (if we are within a function there
  cannot be a need to replace them since we dont extend their context)
- Said join point actually has a replacement parameter registered.
otherwise just return `fvar`.
-/
def replaceFVar (fvar : FVarId) : ExtendM FVarId := do
  if (← read).candidates.contains fvar then
    if let some currentJp := (← read).currentJp? then
      if let some replacement := (← get).fvarMap.find! currentJp |>.find? fvar then
        return replacement.fvarId
  return fvar

/--
Add a new candidate to the current scope + to the list of candidates
if we are currently within a join point. Then execute `x`.
-/
def withNewCandidate (fvar : FVarId) (x : ExtendM α) : ExtendM α := do
  addToScope fvar
  if (← read).currentJp?.isSome then
    withReader (fun ctx => { ctx with candidates := ctx.candidates.insert fvar }) do
      x
  else
    x

/--
Same as `withNewCandidate` but with multiple `FVarId`s.
-/
def withNewCandidates (fvars : Array FVarId) (x : ExtendM α) : ExtendM α := do
  if (← read).currentJp?.isSome then
    let candidates := (← read).candidates
    let folder (acc : FVarIdSet) (val : FVarId) := do
      addToScope val
      return acc.insert val
    let newCandidates ← fvars.foldlM (init := candidates) folder
    withReader (fun ctx => { ctx with candidates := newCandidates }) do
      x
  else
    x

/--
Extend the context of the current join point (if we are within one)
by `fvar` if necessary.
This is necessary if:
- `fvar` is not in scope (that is, was declared outside of the current jp)
- we have not already extended the context by `fvar`
- the list of candidates contains `fvar`. This is because if we have something
  like:
  ```
  let x := ..
  fun f a =>
    jp j b =>
      let y := x
      y
  ```
  There is no point in extending the context of `j` by `x` because we
  cannot lift a join point outside of a local function declaration.
-/
def extendByIfNecessary (fvar : FVarId) : ExtendM Unit := do
  if let some currentJp := (← read).currentJp? then
    let mut translator := (← get).fvarMap.find! currentJp
    let candidates := (← read).candidates
    if !(← isInScope fvar) && !translator.contains fvar && candidates.contains fvar then
      let typ ← getType fvar
      let newParam ← mkAuxParam typ
      translator := translator.insert fvar newParam
      modify fun s => { s with fvarMap := s.fvarMap.insert currentJp translator }

/--
Merge the extended context of two join points if necessary. That is
if we have a structure such as:
```
jp j.1 ... =>
  jp j.2 .. =>
    ...
  ...
```
And we are just done visiting `j.2` we want to extend the context of
`j.1` by all free variables that the context of `j.2` was extended by
as well because we need to drag these variables through at the call sites
of `j.2` in `j.1`.
-/
def mergeJpContextIfNecessary (jp : FVarId) : ExtendM Unit := do
  if (← read).currentJp?.isSome then
    let additionalArgs := (← get).fvarMap.find! jp |>.toArray
    for (fvar, _) in additionalArgs do
      extendByIfNecessary fvar

/--
We call this whenever we enter a new local function. It clears both the
current join point and the list of candidates since we can't lift join
points outside of functions as explained in `mergeJpContextIfNecessary`.
-/
def withNewFunScope (decl : FunDecl) (x : ExtendM α): ExtendM α := do
  withReader (fun ctx => { ctx with currentJp? := none, candidates := {} }) do
    withNewScope do
      x

/--
We call this whenever we enter a new join point. It will set the current
join point and extend the list of candidates by all of the parameters of
the join point. This is so in the case of nested join points that refer
to parameters of the current one we extend the context of the nested
join points by said parameters.
-/
def withNewJpScope (decl : FunDecl) (x : ExtendM α): ExtendM α := do
  withReader (fun ctx => { ctx with currentJp? := some decl.fvarId }) do
    modify fun s => { s with fvarMap := s.fvarMap.insert decl.fvarId {} }
    withNewScope do
      withNewCandidates (decl.params.map (·.fvarId)) do
        x

/--
We call this whenever we visit a new arm of a cases statement.
It will back up the current scope (since we are doing a case split
and want to continue with other arms afterwards) and add all of the
parameters of the match arm to the list of candidates.
-/
def withNewAltScope (alt : Alt) (x : ExtendM α) : ExtendM α := do
  withBackTrackingScope do
    withNewCandidates (alt.getParams.map (·.fvarId)) do
      x

/--
Use all of the above functions to find free variables declared outside
of join points that said join points can be reasonaly extended by. Reasonable
meaning that in case the current join point is nested within a function
declaration we will not extend it by free variables declared before the
function declaration because we cannot lift join points outside of function
declarations.

All of this is done to eliminate dependencies of join points onto their
position within the code so we can pull them out as far as possible, hopefully
enabling new inlining possibilities in the next simplifier run.
-/
partial def extend (decl : Decl) : CompilerM Decl := do
  let newValue ← go decl.value |>.run {} |>.run' {} |>.run' {}
  let decl := { decl with value := newValue }
  decl.pullFunDecls
where
  goFVar (fvar : FVarId) : ExtendM FVarId := do
    extendByIfNecessary fvar
    replaceFVar fvar
  go (code : Code) : ExtendM Code := do
    match code with
    | .let decl k =>
      let decl ← decl.updateValue (← mapFVarM goFVar decl.value)
      withNewCandidate decl.fvarId do
        return Code.updateLet! code decl (← go k)
    | .jp decl k =>
      let decl ← withNewJpScope decl do
        let value ← go decl.value
        let additionalParams := (← get).fvarMap.find! decl.fvarId |>.toArray |>.map Prod.snd
        let newType := additionalParams.foldr (init := decl.type) (fun val acc => .forallE val.binderName val.type acc .default)
        decl.update newType (additionalParams ++ decl.params) value
      mergeJpContextIfNecessary decl.fvarId
      withNewCandidate decl.fvarId do
        return Code.updateFun! code decl (← go k)
    | .fun decl k =>
      let decl ← withNewFunScope decl do
        decl.updateValue (← go decl.value)
      withNewCandidate decl.fvarId do
        return Code.updateFun! code decl (← go k)
    | .cases cs =>
      extendByIfNecessary cs.discr
      let discr ← replaceFVar cs.discr
      let visitor := fun alt => do
        withNewAltScope alt do
          alt.mapCodeM go
      let alts ← cs.alts.mapM visitor
      return Code.updateCases! code cs.resultType discr alts
    | .jmp fn args =>
      let mut newArgs ← args.mapM (mapFVarM goFVar)
      let additionalArgs := (← get).fvarMap.find! fn |>.toArray |>.map Prod.fst
      if let some _currentJp := (← read).currentJp? then
        let f := fun arg => do
          return .fvar (← goFVar arg)
        newArgs := (←additionalArgs.mapM f) ++ newArgs
      else
        newArgs := (additionalArgs.map .fvar) ++ newArgs
      return Code.updateJmp! code fn newArgs
    | .return var =>
      extendByIfNecessary var
      return Code.updateReturn! code (← replaceFVar var)
    | .unreach .. => return code

end JoinPointContextExtender

namespace JoinPointCommonArgs

/--
Context for `ReduceAnalysisM`.
-/
structure AnalysisCtx where
  /--
  The variables that are in scope at the time of the definition of
  the join point.
  -/
  jpScopes : FVarIdMap FVarIdSet := {}

/--
State for `ReduceAnalysisM`.
-/
structure AnalysisState where
  /--
  A map, that for each join point id contains a map from all (so far)
  duplicated argument ids to the respective duplicate value
  -/
  jpJmpArgs : FVarIdMap FVarSubst := {}

abbrev ReduceAnalysisM := ReaderT AnalysisCtx StateRefT AnalysisState ScopeM
abbrev ReduceActionM := ReaderT AnalysisState CompilerM

def isInJpScope (jp : FVarId) (var : FVarId) : ReduceAnalysisM Bool := do
  return (← read).jpScopes.find! jp |>.contains var

open ScopeM

/--
Take a look at each join point and each of their call sites. If all
call sites of a join point have one or more arguments in common, for example:
```
jp _jp.1 a b c => ...
...
cases foo
| n1 => jmp _jp.1 d e f
| n2 => jmp _jp.1 g e h
```
We can get rid of the common argument in favour of inlining it directly
into the join point (in this case the `e`). This reduces the amount of
arguments we have to pass around drastically for example in `ReaderT` based
monad stacks.

Note 1: This transformation can in certain niche cases obtain better results.
For example:
```
jp foo a b => ..
let x := ...
cases discr
| n1 => jmp foo x y
| n2 => jmp foo x z
```
Here we will not collapse the `x` since it is defined after the join point `foo`
and thus not accessible for substitution yet. We could however reorder the code in
such a way that this is possible, this is currently not done since we observe
than in praxis most of the applications of this transformation can occur naturally
without reordering.

Note 2: This transformation is kind of the opposite of `JoinPointContextExtender`.
However we still benefit from the extender because in the `simp` run after it
we might be able to pull join point declarations further up in the hierarchy
of nested functions/join points which in turn might enable additional optimizations.
After we have performed all of these optimizations we can take away the
(remaining) common arguments and end up with nicely floated and optimized
code that has as little arguments as possible in the join points.
-/
partial def reduce (decl : Decl) : CompilerM Decl := do
  let (_, analysis) ← goAnalyze decl.value |>.run {} |>.run {} |>.run' {}
  let newValue ← goReduce decl.value |>.run analysis
  return { decl with value := newValue }
where
  goAnalyzeFunDecl (fn : FunDecl) : ReduceAnalysisM Unit := do
    withNewScope do
      fn.params.forM (addToScope ·.fvarId)
      goAnalyze fn.value

  goAnalyze (code : Code) : ReduceAnalysisM Unit := do
    match code with
    | .let decl k =>
      addToScope decl.fvarId
      goAnalyze k
    | .jp decl k =>
      goAnalyzeFunDecl decl
      let scope ← getScope
      withReader (fun ctx => { ctx with jpScopes := ctx.jpScopes.insert decl.fvarId scope }) do
        addToScope decl.fvarId
        goAnalyze k
    | .fun decl k =>
      goAnalyzeFunDecl decl
      addToScope decl.fvarId
      goAnalyze k
    | .cases cs =>
      let visitor alt := do
        withNewScope do
          alt.getParams.forM (addToScope ·.fvarId)
          goAnalyze alt.getCode
      cs.alts.forM visitor
    | .jmp fn args =>
      let decl ← getFunDecl fn
      if let some knownArgs := (← get).jpJmpArgs.find? fn then
        let mut newArgs := knownArgs
        for (param, arg) in decl.params.zip args do
          if let some knownVal := newArgs.find? param.fvarId then
            if arg.toExpr != knownVal then
              newArgs := newArgs.erase param.fvarId
        modify fun s => { s with jpJmpArgs := s.jpJmpArgs.insert fn newArgs }
      else
        let folder := fun acc (param, arg) => do
          if (← allFVarM (isInJpScope fn) arg) then
            return acc.insert param.fvarId arg.toExpr
          else
            return acc
        let interestingArgs ← decl.params.zip args |>.foldlM (init := {}) folder
        modify fun s => { s with jpJmpArgs := s.jpJmpArgs.insert fn interestingArgs }
    | .return .. | .unreach .. => return ()

  goReduce (code : Code) : ReduceActionM Code := do
    match code with
    | .jp decl k =>
      if let some reducibleArgs := (← read).jpJmpArgs.find? decl.fvarId then
        let filter param := do
          let erasable := reducibleArgs.contains param.fvarId
          if erasable then
            eraseParam param
          return !erasable
        let newParams ← decl.params.filterM filter
        let mut newValue ← goReduce decl.value
        newValue ← replaceFVars newValue reducibleArgs false
        let newType ←
          if newParams.size != decl.params.size then
            mkForallParams newParams (← newValue.inferType)
          else
            pure decl.type
        let k ← goReduce k
        let decl ← decl.update newType newParams newValue
        return Code.updateFun! code decl k
      else
        return Code.updateFun! code decl (← goReduce k)
    | .jmp fn args =>
      let reducibleArgs := (← read).jpJmpArgs.find! fn
      let decl ← getFunDecl fn
      let newParams := decl.params.zip args
        |>.filter (!reducibleArgs.contains ·.fst.fvarId)
        |>.map Prod.snd
      return Code.updateJmp! code fn newParams
    | .let decl k =>
      return Code.updateLet! code decl (← goReduce k)
    | .fun decl k =>
      let decl ← decl.updateValue (← goReduce decl.value)
      return Code.updateFun! code decl (← goReduce k)
    | .cases cs =>
      let alts ← cs.alts.mapM (·.mapCodeM goReduce)
      return Code.updateCases! code cs.resultType cs.discr alts
    | .return .. | .unreach .. => return code

end JoinPointCommonArgs

/--
Find all `fun` declarations in `decl` that qualify as join points then replace
their definitions and call sites with `jp`/`jmp`.
-/
def Decl.findJoinPoints (decl : Decl) : CompilerM Decl := do
  let findResult ← JoinPointFinder.find decl
  trace[Compiler.findJoinPoints] "Found: {findResult.candidates.size} jp candidates"
  JoinPointFinder.replace decl findResult

def findJoinPoints : Pass :=
  .mkPerDeclaration `findJoinPoints Decl.findJoinPoints .base

builtin_initialize
  registerTraceClass `Compiler.findJoinPoints (inherited := true)

def Decl.extendJoinPointContext (decl : Decl) : CompilerM Decl := do
  JoinPointContextExtender.extend decl

def extendJoinPointContext (occurrence : Nat := 0) (phase := Phase.mono) (_h : phase ≠ .base := by simp): Pass :=
  .mkPerDeclaration `extendJoinPointContext Decl.extendJoinPointContext phase (occurrence := occurrence)

builtin_initialize
  registerTraceClass `Compiler.extendJoinPointContext (inherited := true)

def Decl.commonJoinPointArgs (decl : Decl) : CompilerM Decl := do
  JoinPointCommonArgs.reduce decl

def commonJoinPointArgs : Pass :=
  .mkPerDeclaration `commonJoinPointArgs Decl.commonJoinPointArgs .mono

builtin_initialize
  registerTraceClass `Compiler.commonJoinPointArgs (inherited := true)

end Lean.Compiler.LCNF
