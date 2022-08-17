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

abbrev M := StateRefT (Std.HashMap Name Nat) CompilerM

private partial def removeCandidatesContainedIn (e : Expr) : M Unit := do
  let remover := fun fvarId => do
    let some decl ← findDecl? fvarId | unreachable!
    modify (fun jps? => jps?.erase decl.userName)
  forEachFVar e remover

/--
Return a set of let declaration names inside of `e` that qualify as a join
point that is:
1. Are always used in tail position
2. Are always fully applied

Since declaration names are unique inside of LCNF the let bindings and
call sites can be uniquely identified by this.
-/
partial def findJoinPoints (e : Expr) : CompilerM (Array Name) := do
  let (_, names) ← visitLambda goTailApp removeCandidatesContainedIn goLetValue e |>.run .empty
  return names.toArray.map Prod.fst
where
  goLetValue (userName : Name) (value : Expr) : M Expr := do
    if let .lam .. := value then
      withNewScope do
        let (vars, body) ← Compiler.visitLambda value
        modify (fun jps? => jps?.insert userName vars.size)
        visitTails goTailApp removeCandidatesContainedIn goLetValue body
    else
      visitTails goTailApp removeCandidatesContainedIn goLetValue value
    return value

  goTailApp (fvarId : FVarId) (e : Expr) : M Unit := do
    let some decl ← findDecl? fvarId | unreachable!
    if let some jpArity := (←get).find? decl.userName then
      let args := e.getAppNumArgs
      if args != jpArity then
        modify (fun jps? => jps?.erase decl.userName)

end JoinPointFinder

namespace JoinPointChecker

/--
Throws an exception if `e` contains a join point.
-/
def containsNoJp (e : Expr) : CompilerM Unit := do
  trace[Compiler.step] s!"Checking whether {e} contains jp"
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
