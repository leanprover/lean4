/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Compiler.CompilerM

namespace Lean.Compiler

namespace JoinPointChecker

def jpArity (jp : LocalDecl) : Nat :=
  go jp.value
where
  go : Expr → Nat
  | .lam _ _ body _ => 1 + go body
  | _ => 0

/--
Throws an exception if `e` contains a join point.
-/
partial def containsNoJp (e : Expr) : CompilerM Unit := do
  match e.consumeMData with
  | .proj _ _ struct => containsNoJp struct
  | .lam .. =>
    withNewScope do
      let (_, b) ← visitLambda e
      containsNoJp b
  | .letE .. =>
    withNewScope do
      let body ← visitLet e (fun e => do containsNoJp e; pure e)
      containsNoJp body
  | .app fn arg =>
    containsNoJp fn
    containsNoJp arg
  | .fvar fvarId =>
    let some decl ← findDecl? fvarId | unreachable!
    if decl.isJp then
      throwError s!"Join point {decl.userName} in forbidden position"
  | .sort .. | .forallE .. | .const .. | .lit .. => return ()
  | .bvar .. | .mvar .. | .mdata .. => unreachable! 

/--
Check whether all join points in `e` are in a valid position that is:
1. Fully applied
2. In tail position inside of `e`
-/
partial def checkJoinPoints (e : Expr) :  CompilerM Unit := do
  goLambda e
where
  goLambda (e : Expr) : CompilerM Unit := do
    withNewScope do
      let (_, body) ← visitLambda e
      go body

  goLetValue (value : Expr) : CompilerM Unit := do
    let value := value.consumeMData
    match value with
    | .lam .. => goLambda value
    | _ => containsNoJp value

  go (e : Expr) : CompilerM Unit := do
    let e := e.consumeMData
    match e with
    | .letE .. =>
      withNewScope do
        let body ← visitLet e (fun value => do goLetValue value; pure value)
        go body
    | .app (.fvar fvarId) arg =>
      let some decl ← findDecl? fvarId | unreachable!
      if decl.isJp then
        let args := e.getAppNumArgs
        let jpArity := jpArity decl
        if args != jpArity then
          throwError s!"Join point {decl.userName} : {decl.type} is not fully applied in {e}"
      -- Make sure no join point is inside the arguments since that would not be in tail position
      containsNoJp arg
    | .app .. =>
      if let some casesInfo ←isCasesApp? e then
        withNewScope do
          let (motive, discrs, arms) ← visitMatch e casesInfo
          containsNoJp motive
          discrs.forM containsNoJp
          arms.forM go
      else
        containsNoJp e
    | .proj .. | .lam ..  => containsNoJp e
    | .fvar .. | .sort .. | .forallE .. | .const .. | .lit .. => return ()
    | .bvar .. | .mvar .. | .mdata .. => unreachable! 

end JoinPointChecker

end Lean.Compiler
