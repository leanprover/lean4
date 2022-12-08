/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
import Lean.Meta.Check

namespace Lean.Meta

unsafe def evalExprCore (α) (value : Expr) (checkType : Expr → MetaM Unit) (safety := DefinitionSafety.safe) : MetaM α :=
  withoutModifyingEnv do
    let name ← mkFreshUserName `_tmp
    let value ← instantiateMVars value
    if value.hasMVar then
      throwError "failed to evaluate expression, it contains metavariables{indentExpr value}"
    let type ← inferType value
    checkType type
    let decl := Declaration.defnDecl {
       name, levelParams := [], type
       value, hints := ReducibilityHints.opaque,
       safety
    }
    addAndCompile decl
    evalConst α name

unsafe def evalExpr' (α) (typeName : Name) (value : Expr) (safety := DefinitionSafety.safe) : MetaM α :=
  evalExprCore (safety := safety) α value fun type => do
    let type ← whnfD type
    unless type.isConstOf typeName do
      throwError "unexpected type at evalExpr{indentExpr type}"

unsafe def evalExpr (α) (expectedType : Expr) (value : Expr) (safety := DefinitionSafety.safe) : MetaM α :=
  evalExprCore (safety := safety) α value fun type => do
    unless ← isDefEq type expectedType do
      throwError "unexpected type at `evalExpr` {← mkHasTypeButIsExpectedMsg type expectedType}"

end Lean.Meta
