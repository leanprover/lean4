/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PullFunDecls

namespace Lean.Compiler.LCNF

-- TODO: These can be used in a much more general context
partial def mapFVarM [Monad m] (f : FVarId → m FVarId) (e : Expr) : m Expr := do
  match e with
  | .proj typ idx struct => return .proj typ idx (←mapFVarM f struct)
  | .app fn arg => return .app (←mapFVarM f fn) (←mapFVarM f arg)
  | .fvar fvarId => return .fvar (←f fvarId)
  | .lam arg ty body bi =>
    return .lam arg (←mapFVarM f ty) (←mapFVarM f body) bi
  | .forallE arg ty body bi =>
    return .forallE arg (←mapFVarM f ty) (←mapFVarM f body) bi
  | .letE var ty value body nonDep  =>
    return .letE var (←mapFVarM f ty) (←mapFVarM f value) (←mapFVarM f body) nonDep
  | .bvar .. | .sort .. => return e
  | .mdata .. | .const .. | .lit .. => return e
  | .mvar .. => unreachable!

partial def forFVarM [Monad m] (f : FVarId → m Unit) (e : Expr) : m Unit := do
  match e with
  | .proj _ _ struct => forFVarM f struct
  | .app fn arg =>
    forFVarM f fn
    forFVarM f arg
  | .fvar fvarId => f fvarId
  | .lam _ ty body .. =>
    forFVarM f ty
    forFVarM f body
  | .forallE _ ty body .. =>
    forFVarM f ty
    forFVarM f body
  | .letE _ ty value body ..  =>
    forFVarM f ty
    forFVarM f value
    forFVarM f body
  | .bvar .. | .sort .. => return
  | .mdata .. | .const .. | .lit .. => return
  | .mvar .. => unreachable!

/--
A general abstraction for the idea of a scope in the compiler.
-/
abbrev ScopeM := StateRefT FVarIdSet CompilerM

namespace ScopeM

def getScope : ScopeM FVarIdSet := get
def setScope (newScope : FVarIdSet) : ScopeM Unit := set newScope
def clearScope : ScopeM Unit := setScope {}

/--
Execute `x` but recover the previous scope after doing so.
-/
def withBackTrackingScope [MonadLiftT ScopeM m] [Monad m] [MonadFinally m] (x : m α) : m α := do
  let scope ← getScope
  try x finally setScope scope

/--
Clear the current scope for the monadic action `x`, afterwards continuing
with the old one.
-/
def withNewScope [MonadLiftT ScopeM m] [Monad m] [MonadFinally m] (x : m α) : m α := do
  withBackTrackingScope do
    clearScope
    x

/--
Check whether `fvarId` is in the current scope, that is, was declared within
the current `fun` declaration that is being processed.
-/
def isInScope (fvarId : FVarId) : ScopeM Bool := do
  let scope ← getScope
  return scope.contains fvarId

/--
Add a new `FVarId` to the current scope.
-/
def addToScope (fvarId : FVarId) : ScopeM Unit :=
  modify fun scope => scope.insert fvarId

end ScopeM

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
Remove all join point candidates contained in `e`.
-/
private partial def removeCandidatesContainedIn (e : Expr) : FindM Unit := do
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
    match k, decl.value, decl.value.getAppFn with
    | .return valId, .app .., .fvar fvarId =>
      decl.value.getAppArgs.forM removeCandidatesContainedIn
      if let some candidateInfo ← findCandidate? fvarId then
        -- Erase candidate that are not fully applied or applied outside of tail position
        if valId != decl.fvarId || decl.value.getAppNumArgs != candidateInfo.arity then
          eraseCandidate fvarId
        -- Out of scope join point candidate handling
        else if let some upperCandidate ← read then
          if !(←isInScope fvarId) then
            addDependency fvarId upperCandidate
      else
        eraseCandidate fvarId
    | _, _, _ =>
      removeCandidatesContainedIn decl.value
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
  | .jmp _ args => args.forM removeCandidatesContainedIn
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
  let mapper := fun acc cname _ => do return acc.insert cname (←mkFreshJpName)
  let replaceCtx : ReplaceCtx ← state.candidates.foldM (init := .empty) mapper
  let newValue ← go decl.value |>.run replaceCtx
  return { decl with value := newValue }
where
  go (code : Code) : ReplaceM Code := do
    match code with
    | .let decl k =>
      match k, decl.value, decl.value.getAppFn with
      | .return valId, .app .., (.fvar fvarId) =>
        if valId == decl.fvarId then
          if (← read).contains fvarId then
            eraseLetDecl decl
            return .jmp fvarId decl.value.getAppArgs
          else
            return code
        else
          return code
      | _, _, _ => return Code.updateLet! code decl (←go k)
    | .fun decl k =>
      if let some replacement := (← read).find? decl.fvarId then
        let newDecl := { decl with
          binderName := replacement,
          value := (←go decl.value)
        }
        modifyLCtx fun lctx => lctx.addFunDecl newDecl
        return .jp newDecl (←go k)
      else
        let newDecl ← decl.updateValue (←go decl.value)
        return Code.updateFun! code newDecl (←go k)
    | .jp decl k =>
       let newDecl ← decl.updateValue (←go decl.value)
       return Code.updateFun! code newDecl (←go k)
    | .cases cs =>
      return Code.updateCases! code cs.resultType cs.discr (←cs.alts.mapM (·.mapCodeM go))
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
  if (←read).candidates.contains fvar then
    if let some currentJp := (←read).currentJp? then
      if let some replacement := (←get).fvarMap.find! currentJp |>.find? fvar then
        return replacement.fvarId
  return fvar

/--
Add a new candidate to the current scope + to the list of candidates
if we are currently within a join point. Then execute `x`.
-/
def withNewCandidate (fvar : FVarId) (x : ExtendM α) : ExtendM α := do
  addToScope fvar
  if (←read).currentJp?.isSome then
    withReader (fun ctx => { ctx with candidates := ctx.candidates.insert fvar }) do
      x
  else
    x

/--
Same as `withNewCandidate` but with multiple `FVarId`s.
-/
def withNewCandidates (fvars : Array FVarId) (x : ExtendM α) : ExtendM α := do
  if (←read).currentJp?.isSome then
    let candidates := (←read).candidates
    let folder := (fun acc val => do addToScope val; return acc.insert val)
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
  if let some currentJp := (←read).currentJp? then
    let mut translator := (←get).fvarMap.find! currentJp
    let candidates := (←read).candidates
    if !(←isInScope fvar) && !translator.contains fvar && candidates.contains fvar then
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
  if (←read).currentJp?.isSome then
    let additionalArgs := (←get).fvarMap.find! jp |>.toArray
    for (fvar, _) in additionalArgs do
      extendByIfNecessary fvar

/--
We call this whenever we enter a new local function. It clears both the
current join point and the list of candidates since we cant lift join
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
  goExpr (e : Expr) : ExtendM Expr :=
    let visitor := fun fvar => do
      extendByIfNecessary fvar
      replaceFVar fvar
    mapFVarM visitor e
  go (code : Code) : ExtendM Code := do
    match code with
    | .let decl k =>
      let decl ← decl.updateValue (←goExpr decl.value)
      withNewCandidate decl.fvarId do
        return Code.updateLet! code decl (←go k)
    | .jp decl k =>
      let decl ← withNewJpScope decl do
        let value ← go decl.value
        let additionalParams := (←get).fvarMap.find! decl.fvarId |>.toArray |>.map Prod.snd
        let newType := additionalParams.foldr (init := decl.type) (fun val acc => .forallE val.binderName val.type acc .default)
        decl.update newType (additionalParams ++ decl.params) value
      mergeJpContextIfNecessary decl.fvarId
      withNewCandidate decl.fvarId do
        return Code.updateFun! code decl (←go k)
    | .fun decl k =>
      let decl ← withNewFunScope decl do
        decl.updateValue (←go decl.value)
      withNewCandidate decl.fvarId do
        return Code.updateFun! code decl (←go k)
    | .cases cs =>
      extendByIfNecessary cs.discr
      let discr ← replaceFVar cs.discr
      let visitor := fun alt => do
        withNewAltScope alt do
          alt.mapCodeM go
      let alts ← cs.alts.mapM visitor
      return Code.updateCases! code cs.resultType discr alts
    | .jmp fn args =>
      let mut newArgs ← args.mapM goExpr
      let additionalArgs := (←get).fvarMap.find! fn |>.toArray |>.map Prod.fst
      if let some currentJp := (←read).currentJp? then
        let translator := (←get).fvarMap.find! currentJp
        let f := fun arg =>
          if let some translated := translator.find? arg then
            .fvar translated.fvarId
          else
            .fvar arg
        newArgs := (additionalArgs.map f) ++ newArgs
      else
        newArgs := (additionalArgs.map .fvar) ++ newArgs
      return Code.updateJmp! code fn newArgs
    | .return var =>
      extendByIfNecessary var
      return Code.updateReturn! code (←replaceFVar var)
    | .unreach .. => return code

end JoinPointContextExtender

/--
Find all `fun` declarations in `decl` that qualify as join points then replace
their definitions and call sites with `jp`/`jmp`.
-/
def Decl.findJoinPoints (decl : Decl) : CompilerM Decl := do
  let findResult ← JoinPointFinder.find decl
  trace[Compiler.findJoinPoints] s!"Found: {findResult.candidates.size} jp candidates"
  JoinPointFinder.replace decl findResult

def findJoinPoints : Pass :=
  .mkPerDeclaration `findJoinPoints Decl.findJoinPoints .base

builtin_initialize
  registerTraceClass `Compiler.findJoinPoints (inherited := true)

def Decl.extendJoinPointContext (decl : Decl) : CompilerM Decl := do
  JoinPointContextExtender.extend decl

def extendJoinPointContext : Pass :=
  .mkPerDeclaration `extendJoinPointContext Decl.extendJoinPointContext .base

builtin_initialize
  registerTraceClass `Compiler.extendJoinPointContext (inherited := true)

end Lean.Compiler.LCNF
