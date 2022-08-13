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
    let (_, b) ← visitLambda e
    containsNoJp b
  | .letE .. =>
    let body ← visitLet e (fun e => do containsNoJp e; pure e)
    containsNoJp body
  | .app fn arg =>
    containsNoJp fn
    containsNoJp arg
  | .fvar fvarId =>
    let some decl ← findDecl? fvarId | unreachable!
    if decl.userName.getPrefix ==`_jp then
      throwError s!"Join point {decl.userName} in forbidden position"
  | .sort .. | .forallE .. | .const .. | .lit .. => return ()
  | .bvar .. | .mvar .. | .mdata .. => unreachable! 

/--
Obtain all the tail `Expr`s of `e`. Already checking whether non
tail values contain a join point and throwing an exception if they do.
-/
partial def getTails (e : Expr) :  CompilerM (Array Expr) := do
  let (_, body) ← visitLambda e
  let (_, tails) ← go body |>.run #[]
  return tails
where
  goLetValue (value : Expr) : StateRefT (Array Expr) CompilerM Unit := do
    let value := value.consumeMData
    match value with
    | .lam .. =>
      let (_, body) ← visitLambda value
      go body
    | _ =>
      containsNoJp value
      return ()

  go (e : Expr) : StateRefT (Array Expr) CompilerM Unit := do
    let e := e.consumeMData
    match e with
    | .letE .. =>
      let body ← visitLet e (fun value => do goLetValue value; pure value)
      go body
    | .app .. =>
      if let some casesInfo ←isCasesApp? e then
        let (motive, discrs, arms) ← visitMatch e casesInfo
        containsNoJp motive
        discard <| discrs.mapM (liftM ∘ containsNoJp)
        discard <| arms.mapM go
      else
        let tails ← get
        set <| tails.push e
    | .fvar .. | .sort .. | .forallE .. | .const .. | .lit .. | .proj .. | .lam .. =>
      let tails ← get
      set <| tails.push e
    | .bvar .. | .mvar .. | .mdata .. => unreachable! 

/--
Checks that a tail is valid, that is either a fully applied join point
or doesn't contain a join point at all.
-/
def checkTail (e : Expr) : CompilerM Unit := do
  match e with
  | .app (.fvar fvarId) arg =>
    let some decl ← findDecl? fvarId | unreachable!
    if decl.userName.getPrefix == `_jp then
      let args := e.getAppNumArgs
      let jpArity := jpArity decl
      if args != jpArity then
        throwError s!"Join point {decl.userName} : {decl.type} is not fully applied in {e}"
    -- Make sure no join point is inside the arguments since that would not be in tail position
    containsNoJp arg
  /-
   If these are in tail position they may not contain any join point
   since that would mean it is not in tail position.
   Note: the special case where the app function is one is handled above 
  -/
  | .app .. | .proj .. | .lam .. => containsNoJp e
  | .fvar .. | .sort .. | .forallE .. | .const .. | .lit .. => return ()
  | .letE .. | .mdata .. | .bvar .. | .mvar .. => unreachable! 


end JoinPointChecker

end Lean.Compiler
