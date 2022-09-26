/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Instances
import Lean.Compiler.InlineAttrs
import Lean.Compiler.Specialize
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF
/--
Return `true` if the arrow type contains an instance implicit argument.
-/
def hasLocalInst (type : Expr) : Bool :=
  match type with
  | .forallE _ _ b bi => bi.isInstImplicit || hasLocalInst b
  | _ => false

/--
Return `true` if `decl` is supposed to be inlined/specialized.
-/
def Decl.isTemplateLike (decl : Decl) : CoreM Bool := do
  if hasLocalInst decl.type then
    return true -- `decl` applications will be specialized
  else if (← Meta.isInstance decl.name) then
    return true -- `decl` is "fuel" for code specialization
  else if hasInlineAttribute (← getEnv) decl.name || hasSpecializeAttribute (← getEnv) decl.name then
    return true -- `decl` is going to be inlined or specialized
  else
    return false

namespace Simp

partial def findExpr (e : Expr) (skipMData := true) : CompilerM Expr := do
  match e with
  | .fvar fvarId =>
    let some decl ← findLetDecl? fvarId | return e
    findExpr decl.value
  | .mdata _ e' => if skipMData then findExpr e' else return e
  | _ => return e

partial def findFunDecl? (e : Expr) : CompilerM (Option FunDecl) := do
  match e with
  | .fvar fvarId =>
    if let some decl ← LCNF.findFunDecl? fvarId then
      return some decl
    else if let some decl ← findLetDecl? fvarId then
      findFunDecl? decl.value
    else
      return none
  | .mdata _ e => findFunDecl? e
  | _ => return none

end Simp
end Lean.Compiler.LCNF
