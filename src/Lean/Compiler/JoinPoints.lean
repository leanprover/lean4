/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Compiler.CompilerM

namespace Lean.Compiler

def jpArity (jp : LocalDecl) : Nat :=
  getLambdaArity jp.value


namespace JoinPoints

section Visitors

variable {m : Type → Type} [Monad m] [MonadLiftT CompilerM m] [VisitLet m] [MonadFunctorT CompilerM m]

partial def forEachFVar (e : Expr) (f : FVarId → m Unit) : m Unit := do
  let e := e.consumeMData
  match e with
  | .proj _ _ struct => forEachFVar struct f
  | .lam .. =>
    withNewScope do
      let (_, body) ← visitLambda e
      forEachFVar body f
  | .letE .. =>
    withNewScope do
      let body ← visitLet e (fun _ e => do forEachFVar e f; pure e)
      forEachFVar body f
  | .app fn arg =>
    forEachFVar fn f
    forEachFVar arg f
  | .fvar fvarId => f fvarId
  | .sort .. | .forallE .. | .const .. | .lit .. => return ()
  | .bvar .. | .mvar .. | .mdata .. => unreachable!

mutual

variable (tailAppFvarVisitor : FVarId → Expr → m Unit) (valueValidator : Expr → m Unit) (letValueVisitor : Name → Expr → m Expr)

private partial def visitLambda (e : Expr) : m Unit := do
  withNewScope do
    let (_, body) ← Compiler.visitLambda e
    visitTails body

private partial def visitTails (e : Expr) : m Unit := do
  let e := e.consumeMData
  match e with
  | .letE .. =>
    withNewScope do
      let body ← visitLet e letValueVisitor
      visitTails body
  | .app (.fvar fvarId) arg =>
    tailAppFvarVisitor fvarId e
    valueValidator arg
  | .app .. =>
    if let some casesInfo ← (isCasesApp? e : CompilerM (Option CasesInfo)) then
      withNewScope do
        let (motive, discrs, arms) ← visitMatch e casesInfo
        valueValidator motive
        discrs.forM valueValidator
        arms.forM visitTails
    else
      valueValidator e
  | .proj .. | .lam ..  => valueValidator e
  | .fvar .. | .sort .. | .forallE .. | .const .. | .lit .. => return ()
  | .bvar .. | .mvar .. | .mdata .. => unreachable!

end

end Visitors

namespace JoinPointFinder

structure CandidateInfo where
  arity : Nat
  associated : Std.HashSet Name
  deriving Inhabited

abbrev M := ReaderT (Option Name) StateRefT (Std.HashMap Name CandidateInfo) CompilerM

private def findCandidate? (name : Name) : M (Option CandidateInfo) := do
  return (← get).find? name

private partial def eraseCandidate (name : Name) : M Unit := do
  if let some info ← findCandidate? name then
    modify (fun candidates => candidates.erase name)
    info.associated.forM eraseCandidate

private partial def removeCandidatesContainedIn (e : Expr) : M Unit := do
  let remover := fun fvarId => do
    let some decl ← findDecl? fvarId | unreachable!
    eraseCandidate decl.userName
  forEachFVar e remover

private def addCandidate (name : Name) (arity : Nat) : M Unit := do
  let cinfo := { arity, associated := .empty }
  modify (fun cs => cs.insert name cinfo)

private def addDependency (src : Name) (target : Name) : M Unit := do
  if let some targetInfo ← findCandidate? target then
    modify (fun cs => cs.insert target { targetInfo with associated := targetInfo.associated.insert src })
  else
    eraseCandidate src

def declIsInScope (decl : LocalDecl) : CompilerM Bool := do
  let fvars := (←getThe CompilerM.State).letFVars
  fvars.anyM (fun fvar => do
    let scopeDecl := (←findDecl? fvar.fvarId!).get!
    return scopeDecl.userName == decl.userName
  )

/--
Return a set of let declaration names inside of `e` that qualify as a join
point that is:
1. Are always used in tail position
2. Are always fully applied

Since declaration names are unique inside of LCNF the let bindings and
call sites can be uniquely identified by this.
-/
partial def findJoinPoints (e : Expr) : CompilerM (Array Name) := do
  let (_, state) ← visitLambda goTailApp removeCandidatesContainedIn goLetValue e |>.run none |>.run .empty
  return state.toArray.map Prod.fst
where
  goLetValue (userName : Name) (value : Expr) : M Expr := do
    match value with
    | .lam .. => withNewScope do
      let (vars, body) ← Compiler.visitLambda value
      addCandidate userName vars.size
      withReader (fun _ => some userName) do
        visitTails goTailApp removeCandidatesContainedIn goLetValue body
    | _ => removeCandidatesContainedIn value
    return value

  goTailApp (fvarId : FVarId) (e : Expr) : M Unit := do
    let some decl ← findDecl? fvarId | unreachable!
    if let some candidateInfo ← findCandidate? decl.userName then
      let args := e.getAppNumArgs
      if args != candidateInfo.arity then
        eraseCandidate decl.userName
      else if let some upperCandidate ← read then
        if !(←declIsInScope decl) then
          addDependency decl.userName upperCandidate

end JoinPointFinder

namespace JoinPointChecker

/--
Throws an exception if `e` contains a join point.
-/
def containsNoJp (e : Expr) : CompilerM Unit := do
  let checker := fun fvarId => do
    let some decl ← findDecl? fvarId | unreachable!
    if decl.isJp then
      throwError s!"Join point {decl.userName} in forbidden position"
  forEachFVar e checker

/--
Check whether all join points in `e` are in a valid position that is:
1. Fully applied
2. In tail position inside of `e`
-/
partial def checkJoinPoints (e : Expr) :  CompilerM Unit := do
  visitLambda goTailApp containsNoJp goLetValue e

where
  goLetValue (_userName : Name) (value : Expr) : CompilerM Expr := do
    match value with
    | .lam .. => visitLambda goTailApp containsNoJp goLetValue value
    | _ => containsNoJp value
    return value

  goTailApp (fvarId : FVarId) (e : Expr) := do
    let some decl ← findDecl? fvarId | unreachable!
    if decl.isJp then
      let args := e.getAppNumArgs
      let jpArity := jpArity decl
      if args != jpArity then
        throwError s!"Join point {decl.userName} : {decl.type} is not fully applied in {e}"

end JoinPointChecker
end JoinPoints

end Lean.Compiler
