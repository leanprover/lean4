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

private def exprDepOn (e : Expr) : M Bool := do
  let s ← read
  return e.hasAnyFVar fun fvarId => s.contains fvarId

private def LetDecl.depOn (decl : LetDecl) : M Bool :=
  exprDepOn decl.type <||> exprDepOn decl.value

private partial def depOn (c : Code) : M Bool :=
  match c with
  | .let decl k => decl.depOn <||> depOn k
  | .jp decl k | .fun decl k => exprDepOn decl.type <||> depOn decl.value <||> depOn k
  | .cases c => exprDepOn c.resultType <||> fvarDepOn c.discr <||> c.alts.anyM fun alt => depOn alt.getCode
  | .jmp fvarId args => fvarDepOn fvarId <||> args.anyM exprDepOn
  | .return fvarId => fvarDepOn fvarId
  | .unreach _ => return false

abbrev LetDecl.dependsOn (decl : LetDecl) (s : FVarIdSet) :  Bool :=
  decl.depOn s

/--
Return `true` is `c` depends on a free variable in `s`.
-/
def Code.dependsOn (c : Code) (s : FVarIdSet) : Bool :=
  depOn c s

end Lean.Compiler.LCNF
