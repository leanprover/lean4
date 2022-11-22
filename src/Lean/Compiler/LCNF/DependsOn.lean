/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Basic

namespace Lean.Compiler.LCNF

private abbrev M := ReaderT FVarIdSet Id

private def fvarDepOn (fvarId : FVarId) : M Bool :=
  return (← read).contains fvarId

private def typeDepOn (e : Expr) : M Bool := do
  let s ← read
  return e.hasAnyFVar fun fvarId => s.contains fvarId

private def argDepOn (a : Arg) : M Bool := do
  match a with
  | .erased => return false
  | .fvar fvarId => fvarDepOn fvarId
  | .type e => typeDepOn e

private def letValueDepOn (e : LetValue) : M Bool :=
  match e with
  | .erased | .value .. => return false
  | .proj _ _ fvarId => fvarDepOn fvarId
  | .fvar fvarId args => fvarDepOn fvarId <||> args.anyM argDepOn
  | .const _ _ args => args.anyM argDepOn

private def LetDecl.depOn (decl : LetDecl) : M Bool :=
  typeDepOn decl.type <||> letValueDepOn decl.value

private partial def depOn (c : Code) : M Bool :=
  match c with
  | .let decl k => decl.depOn <||> depOn k
  | .jp decl k | .fun decl k => typeDepOn decl.type <||> depOn decl.value <||> depOn k
  | .cases c => typeDepOn c.resultType <||> fvarDepOn c.discr <||> c.alts.anyM fun alt => depOn alt.getCode
  | .jmp fvarId args => fvarDepOn fvarId <||> args.anyM argDepOn
  | .return fvarId => fvarDepOn fvarId
  | .unreach _ => return false

abbrev LetDecl.dependsOn (decl : LetDecl) (s : FVarIdSet) :  Bool :=
  decl.depOn s

abbrev FunDecl.dependsOn (decl : FunDecl) (s : FVarIdSet) :  Bool :=
  typeDepOn decl.type s || depOn decl.value s

def CodeDecl.dependsOn (decl : CodeDecl) (s : FVarIdSet) : Bool :=
  match decl with
  | .let decl => decl.dependsOn s
  | .jp decl | .fun decl => decl.dependsOn s

/--
Return `true` is `c` depends on a free variable in `s`.
-/
def Code.dependsOn (c : Code) (s : FVarIdSet) : Bool :=
  depOn c s

end Lean.Compiler.LCNF
