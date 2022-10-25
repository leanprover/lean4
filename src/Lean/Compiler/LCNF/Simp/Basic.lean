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
namespace Simp

/-
-- TODO: cleanup
partial def findExpr (e : LetExpr) : CompilerM LetExpr := do
  match e with
  | .fvar fvarId args =>
    if args.isEmpty then
      let some decl ← findLetDecl? fvarId | return e
      findExpr decl.value
    else
      return e
  | _ => return e

partial def findFunDecl? (e : LetExpr) : CompilerM (Option FunDecl) := do
  match e with
  | .fvar fvarId args =>

    if let some decl ← LCNF.findFunDecl? fvarId then
      return some decl
    else if let some decl ← findLetDecl? fvarId then
      findFunDecl? decl.value
    else
      return none
  | _ => return none
-/
end Simp
end Lean.Compiler.LCNF
