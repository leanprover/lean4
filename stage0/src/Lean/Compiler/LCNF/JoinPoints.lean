/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF

namespace JoinPointFinder

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

abbrev FindM := ReaderT (Option FVarId) StateRefT FindState CompilerM
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
  match e with
  | .proj _ _ struct => removeCandidatesContainedIn struct
  | .app fn arg =>
    removeCandidatesContainedIn fn
    removeCandidatesContainedIn arg
  | .fvar fvarId => eraseCandidate fvarId
  -- These cannot occur in (computationally relevant) LCNF
  | .bvar .. | .lam .. | .sort .. | .forallE .. | .letE .. => return
  -- These we just don't care about
  | .mdata .. | .const .. | .lit .. => return
  | .mvar .. => unreachable!

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
Clear the current scope for the monadic action `x`, afterwards continuing
with the old one.
-/
private def withNewScope (x : FindM α) : FindM α := do
  let scope := (← get).scope
  modify fun s => { s with scope := {} }
  try x finally modify fun s => { s with scope }

/--
Check whether `fvarId` is in the current scope, that is, was declared within
the current `fun` declaration that is being processed.
-/
private def isInScope (fvarId : FVarId) : FindM Bool := do
  let scope := (← get).scope
  return scope.contains fvarId

/--
Add a new `FVarId` to the current scope.
-/
private def addToScope (fvarId : FVarId) : FindM Unit :=
  modify fun state => { state with scope := state.scope.insert fvarId }

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
  let (_, candidates) ← go decl.value |>.run none |>.run {}
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

end Lean.Compiler.LCNF
