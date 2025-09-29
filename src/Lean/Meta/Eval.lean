/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
module

prelude
public import Lean.AddDecl
public import Lean.Meta.Check
public import Lean.Util.CollectLevelParams

public section

namespace Lean.Meta

unsafe def evalExprCore (α) (value : Expr) (checkType : Expr → MetaM Unit)
    (safety := DefinitionSafety.safe) (checkMeta : Bool := true) : MetaM α :=
  withoutModifyingEnv do
    -- Avoid waiting for all prior compilation if only imported constants are referenced. This is a
    -- very common case for tactic configurations (`Lean.Elab.Tactic.Config`).
    if value.getUsedConstants.all (← getEnv).isImportedConst then
      modifyEnv fun env => env.importEnv?.getD env

    let name ← mkFreshUserName `_tmp
    let value ← instantiateMVars value
    let us := collectLevelParams {} value |>.params
    if value.hasMVar then
      throwError "failed to evaluate expression, it contains metavariables{indentExpr value}"
    let type ← inferType value
    checkType type
    let decl := Declaration.defnDecl {
       name, levelParams := us.toList, type
       value, hints := ReducibilityHints.opaque,
       safety
    }
    -- compilation will invariably wait on `checked`
    let _ ← traceBlock "compiler env" (← getEnv).checked
    -- now that we've already waited, async would just introduce (minor) overhead and trigger
    -- `Task.get` blocking debug code
    withOptions (Elab.async.set · false) do
      addAndCompile decl
      evalConst (checkMeta := checkMeta) α name

unsafe def evalExpr' (α) (typeName : Name) (value : Expr) (safety := DefinitionSafety.safe)
    (checkMeta : Bool := true) : MetaM α :=
  evalExprCore (safety := safety) (checkMeta := checkMeta) α value fun type => do
    let type ← whnfD type
    unless type.isConstOf typeName do
      throwError "unexpected type at evalExpr{indentExpr type}"

unsafe def evalExpr (α) (expectedType : Expr) (value : Expr) (safety := DefinitionSafety.safe)
    (checkMeta : Bool := true) : MetaM α :=
  evalExprCore (safety := safety) (checkMeta := checkMeta) α value fun type => do
    unless ← isDefEq type expectedType do
      throwError "unexpected type at `evalExpr` {← mkHasTypeButIsExpectedMsg type expectedType}"

end Lean.Meta
